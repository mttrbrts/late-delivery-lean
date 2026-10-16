/**
 * Differential test harness: the verified Lean model is the oracle.
 *
 *   node --experimental-strip-types ts/harness.ts [N] [SEED]
 *
 * 1. Asks the Lean binary for N test vectors (inputs + expected outputs).
 * 2. Runs `logic.ts` on the same inputs.
 * 3. Reports disagreements, tagged with the features present in the failing cases.
 *
 * Exit code is non-zero if `logic.ts` disagrees anywhere, so this can run in a
 * template's CI.
 */
import { spawnSync } from 'node:child_process';
import { LEAN_BIN } from './leanRuntime.ts';
import * as spec from './logic.ts';

type Outcome = { error: true } | { error: false; penaltyMinor: number; terminate: boolean };
type Impl = (d: any, r: any, now: string) => spec.LateDeliveryResponse;

const N = Number(process.argv[2] ?? 5000);
const SEED = Number(process.argv[3] ?? 42);

function vectors(basis: string): any[] {
  const run = spawnSync(LEAN_BIN, ['vectors', String(N), String(SEED), basis], {
    encoding: 'utf8',
    maxBuffer: 1 << 30,
  });
  if (run.status !== 0) throw new Error(`lean vectors failed: ${run.stderr}`);
  return JSON.parse(run.stdout);
}

function expected(v: any): Outcome {
  if (v.expected.error) return { error: true };
  const r = v.expected.result;
  return { error: false, penaltyMinor: Math.round(r.penalty * 100), terminate: r.buyerMayTerminate };
}

function actual(impl: Impl, v: any): Outcome {
  try {
    const r = impl(v.data, v.request, v.now);
    if (!Number.isFinite(r.penalty)) return { error: false, penaltyMinor: NaN, terminate: r.buyerMayTerminate };
    return { error: false, penaltyMinor: Math.round(r.penalty * 100), terminate: r.buyerMayTerminate };
  } catch {
    return { error: true };
  }
}

/** Features of a case, used to explain why implementations disagree. */
function tags(v: any): string[] {
  const t: string[] = [];
  const { data: d, request: r, now } = v;
  const effective = Date.parse(r.deliveredAt ?? now);
  const delayMs = effective - Date.parse(r.agreedDelivery);
  if (r.deliveredAt) t.push('delivered before now (deliveredAt ignored?)');
  if (d.termination.unit !== 'days') t.push(`termination in ${d.termination.unit} (unit ignored?)`);
  if (d.penaltyDuration.unit !== 'days') t.push(`penaltyDuration in ${d.penaltyDuration.unit} (unit ignored?)`);
  if (d.penaltyDuration.amount === 0) t.push('zero penalty period');
  if (d.forceMajeure && r.forceMajeure) t.push('force majeure applies');
  if (delayMs > 0 && delayMs % 86_400_000 !== 0) t.push('part-day delay (rounding up?)');
  if (delayMs <= 0) t.push('not late');
  return t;
}

function diffKind(e: Outcome, a: Outcome): string[] {
  if (e.error !== a.error) return [e.error ? 'ran when it should reject' : 'rejected a valid case'];
  if (e.error || a.error) return [];
  const k: string[] = [];
  if (Number.isNaN(a.penaltyMinor)) k.push('penalty is NaN/Infinity');
  else if (a.penaltyMinor !== e.penaltyMinor)
    k.push(Math.abs(a.penaltyMinor - e.penaltyMinor) <= 1 ? 'penalty off by 1 minor unit (rounding)' : 'penalty differs');
  if (a.terminate !== e.terminate) k.push('termination right differs');
  return k;
}

function check(name: string, impl: Impl, cases: any[]) {
  let bad = 0;
  const byKind = new Map<string, number>();
  const byTag = new Map<string, number>();
  let example: any = null;
  for (const v of cases) {
    const kinds = diffKind(expected(v), actual(impl, v));
    if (kinds.length === 0) continue;
    bad++;
    for (const k of kinds) byKind.set(k, (byKind.get(k) ?? 0) + 1);
    for (const t of tags(v)) byTag.set(t, (byTag.get(t) ?? 0) + 1);
    example ??= { input: { data: v.data, request: v.request, now: v.now }, expected: v.expected, got: (() => { try { return impl(v.data, v.request, v.now); } catch (e: any) { return { error: e.message }; } })() };
  }
  const pct = ((100 * bad) / cases.length).toFixed(1);
  console.log(`\n${name}: ${cases.length - bad}/${cases.length} agree with Lean (${pct}% disagree)`);
  const sorted = (m: Map<string, number>) => [...m].sort((a, b) => b[1] - a[1]);
  for (const [k, n] of sorted(byKind)) console.log(`  ${String(n).padStart(6)}  ${k}`);
  if (byTag.size) {
    console.log('  features present in disagreeing cases:');
    for (const [k, n] of sorted(byTag)) console.log(`  ${String(n).padStart(6)}  ${k}`);
  }
  if (example && process.env.SHOW_EXAMPLE) console.log('  first disagreement:', JSON.stringify(example, null, 2));
  return bad;
}

console.log(`Lean oracle: ${LEAN_BIN}\nvectors: ${N} per suite, seed ${SEED}`);

const mixed = vectors('mixed');
const specBad = check('logic.ts, all accrual bases', spec.trigger, mixed);

process.exitCode = specBad === 0 ? 0 : 1;
