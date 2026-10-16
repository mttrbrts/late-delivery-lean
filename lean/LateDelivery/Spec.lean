/-!
# Late Delivery and Penalty — executable specification

A Lean model of the Accord Project "Late Delivery and Penalty" clause.

Clause text (template `latedeliveryandpenalty`):

> In case of delayed delivery [except for Force Majeure cases,] the Seller shall pay
> to the Buyer for every {penaltyDuration} of delay penalty amounting to
> {penaltyPercentage}% of the total value of the Equipment whose delivery has been
> delayed. Any fractional part of a {fractionalPart} is to be considered a full
> {fractionalPart}. The total amount of penalty shall not however, exceed
> {capPercentage}% of the total value of the Equipment involved in late delivery.
> If the delay is more than {termination}, the Buyer is entitled to terminate this
> Contract.

Modelling decisions (each one is a question the prose leaves open):

* **Exact arithmetic.** Money is in minor units (pence/cents), percentages are basis
  points (10.5% = 1050), time is Unix milliseconds. No floating point anywhere.
* **Units are normalised.** Durations are converted to days before they reach the
  logic, so "2 weeks" means 14 days.
* **Fractional days round up** ("any fractional part of a day is a full day").
* **Money rounds down** to the minor unit (in the Seller's favour). This is a choice;
  the clause is silent.
* **"For every N days" is ambiguous**, so the accrual `Basis` is a parameter:
  - `proportional`     — pro rata (the default)
  - `completedPeriods` — only whole elapsed periods count
  - `startedPeriods`   — any started period counts in full
* **Force majeure** (when the contract includes it and it applies) removes the
  penalty only. The text does not say it creates a termination right.
* **"More than"** is strict: delay > termination.
* **The effective date** is `deliveredAt` if delivered, otherwise `now`.
-/

namespace LateDelivery

/-- How penalty accrues for "every penaltyDuration of delay". -/
inductive Basis where
  | proportional
  | completedPeriods
  | startedPeriods
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Contract parameters (the template model), already normalised. -/
structure Contract where
  forceMajeure    : Bool
  periodDays      : Nat     -- penaltyDuration in days
  penaltyBp       : Nat     -- penaltyPercentage in basis points
  capBp           : Nat     -- capPercentage in basis points
  terminationDays : Nat     -- termination in days
  basis           : Basis := .proportional
  deriving Repr, Inhabited

/-- A late delivery request. -/
structure Request where
  forceMajeure   : Bool
  agreedDelivery : Int          -- Unix milliseconds
  deliveredAt    : Option Int   -- Unix milliseconds
  goodsValue     : Nat          -- minor units
  deriving Repr, Inhabited

structure Response where
  penalty           : Nat       -- minor units
  buyerMayTerminate : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

def msPerDay : Nat := 86400000

/-- Integer division rounding up. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Whole days of delay; a fractional day counts as a full day. -/
def delayDays (agreed effective : Int) : Nat :=
  ceilDiv (effective - agreed).toNat msPerDay

/-- Uncapped penalty for `days` of delay on goods worth `value`. -/
def rawPenalty (c : Contract) (days value : Nat) : Nat :=
  match c.basis with
  | .proportional     => value * c.penaltyBp * days / (10000 * c.periodDays)
  | .completedPeriods => value * c.penaltyBp * (days / c.periodDays) / 10000
  | .startedPeriods   => value * c.penaltyBp * ceilDiv days c.periodDays / 10000

/-- The maximum penalty the contract allows. -/
def cap (c : Contract) (value : Nat) : Nat := value * c.capBp / 10000

/-- Penalty after force majeure and the cap. -/
def penalty (c : Contract) (fmApplies : Bool) (days value : Nat) : Nat :=
  if fmApplies then 0 else min (rawPenalty c days value) (cap c value)

def mayTerminate (c : Contract) (days : Nat) : Bool := decide (days > c.terminationDays)

/-- A contract is well formed when the penalty period is positive. -/
def Contract.valid (c : Contract) : Prop := 0 < c.periodDays

instance (c : Contract) : Decidable c.valid := inferInstanceAs (Decidable (0 < c.periodDays))

def tooEarlyMsg : String := "Cannot exercise late delivery before delivery date"
def invalidMsg  : String := "Invalid contract: penaltyDuration must be positive"

/-- The clause logic: the analogue of `trigger` in an Accord template. -/
def trigger (c : Contract) (r : Request) (now : Int) : Except String Response :=
  if c.periodDays = 0 then .error invalidMsg
  else
    let effective := r.deliveredAt.getD now
    if effective ≤ r.agreedDelivery then .error tooEarlyMsg
    else
      let days := delayDays r.agreedDelivery effective
      let fm   := c.forceMajeure && r.forceMajeure
      .ok { penalty := penalty c fm days r.goodsValue
            buyerMayTerminate := mayTerminate c days }

end LateDelivery
