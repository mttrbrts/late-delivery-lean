import LateDelivery

/-!
# `latedelivery` — the clause as a standalone runtime

    latedelivery trigger                 # reads {data, request, now} JSON on stdin
    latedelivery vectors N SEED [BASIS]  # prints N test vectors with expected results

BASIS is `proportional` (default), `completedPeriods`, `startedPeriods` or `mixed`.
-/

open Lean (Json JsonNumber)
open LateDelivery LateDelivery.Json

/-- Tiny deterministic PRNG (64-bit LCG) so vectors are reproducible from a seed. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) (bound : Nat) : Nat × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % (max bound 1), ⟨s⟩)

def duration (amount : Nat) (unit : String) : Json :=
  Json.mkObj [("$class", "org.accordproject.time.Duration"),
              ("amount", Json.num (amount : Int)), ("unit", Json.str unit)]

def pct (bp : Nat) : Json := Json.num { mantissa := bp, exponent := 2 }

def basisName : Basis → String
  | .proportional => "proportional"
  | .completedPeriods => "completedPeriods"
  | .startedPeriods => "startedPeriods"

/-- One random test case. Biased towards the boundaries that matter: exact whole
days of delay, delays around the termination threshold, zero values, force majeure. -/
def genCase (g : Rng) (basisMode : String) : Json × Rng := Id.run do
  let mut g := g
  let roll (b : Nat) : StateM Rng Nat := fun g => g.next b
  let ((periodAmt, periodUnit, pBp, cBp, termAmt, termUnit, cFm, rFm,
        basisIx, agreedOff, delayKind, delayDays, delayMs, delivered, extra, value), g') :=
    (do
      let pu ← roll 4
      let pa ← if pu == 0 then (· + 1) <$> roll 2 else roll 15   -- 0 occasionally: invalid
      let pBp ← roll 2001
      let cBp ← (fun n => if n % 7 == 0 then 10000 else n) <$> roll 10001
      let tu ← roll 3
      let ta ← if tu == 0 then (· + 1) <$> roll 4 else (· + 1) <$> roll 30
      let cFm ← (· == 0) <$> roll 2
      let rFm ← (· == 0) <$> roll 4
      let bIx ← roll 3
      let ao ← roll (365 * 86400)
      let dk ← roll 4
      let dd ← roll 62
      let dm ← roll 86400000
      let del ← (· == 0) <$> roll 2
      let ex ← roll (10 * 86400)
      let v ← (fun n => if n % 13 == 0 then 0 else n) <$> roll 10000001
      pure (pa, (if pu == 0 then "weeks" else "days"), pBp, cBp, ta,
            (if tu == 0 then "weeks" else "days"), cFm, rFm, bIx, ao, dk, dd, dm, del, ex, v)
    ).run g
  g := g'
  let basis : Basis := match basisMode with
    | "completedPeriods" => .completedPeriods
    | "startedPeriods" => .startedPeriods
    | "mixed" => if basisIx == 0 then .proportional else if basisIx == 1 then .completedPeriods else .startedPeriods
    | _ => .proportional
  let agreed : Int := (daysFromCivil 2026 1 1) * 86400000 + (agreedOff : Int) * 1000
  -- delay: exact whole days, whole days minus/plus a little, or arbitrary; some negative
  let delay : Int := match delayKind with
    | 0 => (delayDays : Int) * 86400000
    | 1 => (delayDays : Int) * 86400000 + 1000
    | 2 => (delayDays : Int) * 86400000 - (delayMs : Int) / 1000 * 1000
    | _ => (delayDays : Int) * 86400000 - 2 * 86400000 + (delayMs : Int) / 1000 * 1000
  let effective := agreed + delay
  let now := if delivered then effective + (extra : Int) * 1000 else effective
  let mut data := Json.mkObj [
    ("$class", "org.accordproject.latedeliveryandpenalty.TemplateModel"),
    ("clauseId", "vector"),
    ("forceMajeure", Json.bool cFm),
    ("penaltyDuration", duration periodAmt periodUnit),
    ("penaltyPercentage", pct pBp),
    ("capPercentage", pct cBp),
    ("termination", duration termAmt termUnit),
    ("fractionalPart", "days")]
  if basisMode == "mixed" || basis != .proportional then
    data := data.setObjVal! "accrualBasis" (basisName basis)
  let request := Json.mkObj [
    ("$class", "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyRequest"),
    ("forceMajeure", Json.bool rFm),
    ("agreedDelivery", Json.str (formatIso agreed)),
    ("deliveredAt", if delivered then Json.str (formatIso effective) else Json.null),
    ("goodsValue", money value)]
  let env := Json.mkObj [("data", data), ("request", request), ("now", Json.str (formatIso now))]
  let expected := runEnvelope env
  (env.setObjVal! "expected" expected, g)

def vectors (n seed : Nat) (basisMode : String) : Json := Id.run do
  let mut g : Rng := ⟨seed.toUInt64⟩
  let mut out : Array Json := #[]
  for _ in [0:n] do
    let (c, g') := genCase g basisMode
    out := out.push c
    g := g'
  Json.arr out

def main (args : List String) : IO UInt32 := do
  match args with
  | ["trigger"] =>
    let input ← (← IO.getStdin).readToEnd
    match Json.parse input with
    | .ok env => IO.println (runEnvelope env).compress; return 0
    | .error e => IO.println (Json.mkObj [("error", Json.str s!"bad JSON: {e}")]).compress; return 1
  | "vectors" :: n :: seed :: rest =>
    match n.toNat?, seed.toNat? with
    | some n, some seed =>
      IO.println (vectors n seed (rest.headD "proportional")).compress; return 0
    | _, _ => IO.eprintln "usage: latedelivery vectors N SEED [BASIS]"; return 2
  | _ =>
    IO.eprintln "usage: latedelivery trigger < envelope.json\n       latedelivery vectors N SEED [BASIS]"
    return 2
