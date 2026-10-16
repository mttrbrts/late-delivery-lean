/**
 * Late Delivery and Penalty — TypeScript logic written to the Lean specification.
 *
 * This is the kind of `logic/logic.ts` a template author ships today. It is NOT
 * trusted on its own: `harness.ts` checks it against test vectors produced by the
 * verified Lean model. In a template archive the `trigger` below would be the body
 * of `class LateDeliveryLogic extends TemplateLogic<TemplateModel>`.
 *
 * Rules (see lean/LateDelivery/Spec.lean for the reasoning):
 *  - money in minor units, percentages in basis points, BigInt arithmetic
 *  - durations normalised to days ("2 weeks" = 14 days)
 *  - a fractional day of delay counts as a full day
 *  - money rounds down to the minor unit
 *  - force majeure removes the penalty only
 *  - effective date = deliveredAt if delivered, else now
 */

export type Duration = { amount: number; unit: string };

export type TemplateModel = {
  forceMajeure: boolean;
  penaltyDuration: Duration;
  penaltyPercentage: number;
  capPercentage: number;
  termination: Duration;
  accrualBasis?: 'proportional' | 'completedPeriods' | 'startedPeriods';
};

export type LateDeliveryRequest = {
  forceMajeure: boolean;
  agreedDelivery: string;
  deliveredAt?: string | null;
  goodsValue: number;
};

export type LateDeliveryResponse = {
  $class: 'org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyResponse';
  penalty: number;
  buyerMayTerminate: boolean;
};

const MS_PER_DAY = 86_400_000;

/** Convert a decimal with at most two places to an exact integer scaled by 100. */
function hundredths(what: string, x: number): bigint {
  if (!(x >= 0)) throw new Error(`${what} must not be negative`);
  const scaled = Math.round(x * 100);
  if (Math.abs(scaled - x * 100) > 1e-6) throw new Error(`${what} has more than 2 decimal places`);
  return BigInt(scaled);
}

function days(what: string, d: Duration): bigint {
  if (!Number.isInteger(d.amount) || d.amount < 0) throw new Error(`${what}.amount must be a whole number`);
  if (d.unit === 'days') return BigInt(d.amount);
  if (d.unit === 'weeks') return 7n * BigInt(d.amount);
  throw new Error(`${what}: unsupported unit '${d.unit}' (expected days or weeks)`);
}

function parseTime(s: string): bigint {
  const t = Date.parse(s);
  if (Number.isNaN(t)) throw new Error(`unsupported timestamp '${s}'`);
  return BigInt(t);
}

const ceilDiv = (a: bigint, b: bigint) => (a + b - 1n) / b;
const min = (a: bigint, b: bigint) => (a < b ? a : b);

export function trigger(data: TemplateModel, request: LateDeliveryRequest, now: string): LateDeliveryResponse {
  const periodDays = days('penaltyDuration', data.penaltyDuration);
  const terminationDays = days('termination', data.termination);
  const penaltyBp = hundredths('penaltyPercentage', data.penaltyPercentage);
  const capBp = hundredths('capPercentage', data.capPercentage);
  const value = hundredths('goodsValue', request.goodsValue);
  const agreed = parseTime(request.agreedDelivery);
  const effective = request.deliveredAt ? parseTime(request.deliveredAt) : parseTime(now);

  if (periodDays === 0n) throw new Error('Invalid contract: penaltyDuration must be positive');
  if (effective <= agreed) throw new Error('Cannot exercise late delivery before delivery date');

  const delayDays = ceilDiv(effective - agreed, BigInt(MS_PER_DAY));

  let raw: bigint;
  switch (data.accrualBasis ?? 'proportional') {
    case 'proportional':
      raw = (value * penaltyBp * delayDays) / (10000n * periodDays);
      break;
    case 'completedPeriods':
      raw = (value * penaltyBp * (delayDays / periodDays)) / 10000n;
      break;
    case 'startedPeriods':
      raw = (value * penaltyBp * ceilDiv(delayDays, periodDays)) / 10000n;
      break;
    default:
      throw new Error(`unknown accrualBasis '${data.accrualBasis}'`);
  }
  const cap = (value * capBp) / 10000n;
  const fm = data.forceMajeure && request.forceMajeure;
  const penalty = fm ? 0n : min(raw, cap);

  return {
    $class: 'org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyResponse',
    penalty: Number(penalty) / 100,
    buyerMayTerminate: delayDays > terminationDays,
  };
}
