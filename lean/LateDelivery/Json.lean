import Lean.Data.Json
import LateDelivery.Spec

/-!
# Concerto JSON boundary

Reads the template's Concerto JSON (contract data and request) into the exact
integer model, and writes the response back as Concerto JSON.

* Decimal numbers are converted exactly using the JSON literal's own digits,
  never via floating point. A value with more precision than the model holds
  (e.g. 10.505%) is rejected rather than silently rounded.
* Durations are normalised to days; units other than days or weeks are rejected.
* Timestamps are ISO 8601 (`2017-12-17T03:24:00Z`, optional fractional seconds,
  `Z` or `±HH:MM` offset), converted to Unix milliseconds.
-/

namespace LateDelivery.Json
open Lean (Json JsonNumber)

/-- Convert a JSON decimal to a natural number scaled by `10^k`, exactly. -/
def scaled (what : String) (n : JsonNumber) (k : Nat) : Except String Nat := do
  if n.mantissa < 0 then throw s!"{what} must not be negative"
  let num := n.mantissa.toNat * 10 ^ k
  let den := 10 ^ n.exponent
  if num % den ≠ 0 then throw s!"{what} has more than {k} decimal places"
  return num / den

def getNum (j : Json) (key : String) : Except String JsonNumber := do
  (← j.getObjVal? key).getNum?

/-- Normalise a Concerto `Duration` to days. -/
def durationDays (what : String) (j : Json) : Except String Nat := do
  let amount ← scaled s!"{what}.amount" (← getNum j "amount") 0
  match ← (← j.getObjVal? "unit").getStr? with
  | "days"  => return amount
  | "weeks" => return 7 * amount
  | u       => throw s!"{what}: unsupported unit '{u}' (expected days or weeks)"

/-! ## Calendar arithmetic (proleptic Gregorian, H. Hinnant's algorithms) -/

def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400, m, d)

def digits (what : String) (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => if s.all Char.isDigit then pure n else throw s!"bad {what} in timestamp"
  | none   => throw s!"bad {what} in timestamp"

/-- Parse an ISO 8601 timestamp to Unix milliseconds. -/
def parseIso (s : String) : Except String Int := do
  let bad := s!"unsupported timestamp '{s}'"
  if s.length < 20 || s.get ⟨10⟩ != 'T' then throw bad
  let y  ← digits "year"   ((s.drop 0).take 4)
  let mo ← digits "month"  ((s.drop 5).take 2)
  let d  ← digits "day"    ((s.drop 8).take 2)
  let h  ← digits "hour"   ((s.drop 11).take 2)
  let mi ← digits "minute" ((s.drop 14).take 2)
  let se ← digits "second" ((s.drop 17).take 2)
  let mut rest := s.drop 19
  let mut ms : Nat := 0
  if rest.startsWith "." then
    let frac := (rest.drop 1).takeWhile Char.isDigit
    if frac.isEmpty then throw bad
    ms ← digits "fraction" ((frac ++ "00").take 3)
    rest := (rest.drop 1).dropWhile Char.isDigit
  let offsetMin : Int ← match rest.get? 0 with
    | some 'Z' => if rest.length == 1 then pure 0 else throw bad
    | some c =>
      if (c == '+' || c == '-') && rest.length == 6 && rest.get ⟨3⟩ == ':' then do
        let oh ← digits "offset" ((rest.drop 1).take 2)
        let om ← digits "offset" ((rest.drop 4).take 2)
        let o : Int := oh * 60 + om
        pure (if c == '-' then -o else o)
      else throw bad
    | none => throw bad
  let days := daysFromCivil y mo d
  let secs := days * 86400 + h * 3600 + mi * 60 + se - offsetMin * 60
  return secs * 1000 + ms

def pad (n : Nat) (w : Nat) : String :=
  let s := toString n
  "".pushn '0' (w - s.length) ++ s

/-- Format Unix milliseconds as `YYYY-MM-DDTHH:MM:SS.sssZ`. -/
def formatIso (t : Int) : String :=
  let days := t / 86400000
  let msInDay := (t - days * 86400000).toNat
  let (y, m, d) := civilFromDays days
  let sod := msInDay / 1000
  s!"{pad y.toNat 4}-{pad m.toNat 2}-{pad d.toNat 2}T{pad (sod / 3600) 2}:{pad (sod % 3600 / 60) 2}:{pad (sod % 60) 2}.{pad (msInDay % 1000) 3}Z"

/-! ## Template data, request and response -/

def parseBasis (j : Json) : Except String Basis :=
  match j.getObjVal? "accrualBasis" with
  | .error _ => pure .proportional
  | .ok v => do
    match ← v.getStr? with
    | "proportional"     => pure .proportional
    | "completedPeriods" => pure .completedPeriods
    | "startedPeriods"   => pure .startedPeriods
    | b => throw s!"unknown accrualBasis '{b}'"

def parseContract (j : Json) : Except String Contract := do
  return {
    forceMajeure    := ← (← j.getObjVal? "forceMajeure").getBool?
    periodDays      := ← durationDays "penaltyDuration" (← j.getObjVal? "penaltyDuration")
    penaltyBp       := ← scaled "penaltyPercentage" (← getNum j "penaltyPercentage") 2
    capBp           := ← scaled "capPercentage" (← getNum j "capPercentage") 2
    terminationDays := ← durationDays "termination" (← j.getObjVal? "termination")
    basis           := ← parseBasis j }

def parseRequest (j : Json) : Except String Request := do
  let delivered ← match j.getObjVal? "deliveredAt" with
    | .ok Json.null => pure none
    | .ok v => some <$> (parseIso (← v.getStr?))
    | .error _ => pure none
  return {
    forceMajeure   := ← (← j.getObjVal? "forceMajeure").getBool?
    agreedDelivery := ← parseIso (← (← j.getObjVal? "agreedDelivery").getStr?)
    deliveredAt    := delivered
    goodsValue     := ← scaled "goodsValue" (← getNum j "goodsValue") 2 }

def money (minor : Nat) : Json := Json.num { mantissa := minor, exponent := 2 }

def responseJson (r : Response) : Json :=
  Json.mkObj [
    ("$class", "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyResponse"),
    ("penalty", money r.penalty),
    ("buyerMayTerminate", Json.bool r.buyerMayTerminate) ]

/-- Run the clause on a `{ data, request, now }` envelope. -/
def runEnvelope (env : Json) : Json :=
  let out : Except String Response := do
    let c ← parseContract (← env.getObjVal? "data")
    let r ← parseRequest (← env.getObjVal? "request")
    let now ← parseIso (← (← env.getObjVal? "now").getStr?)
    trigger c r now
  match out with
  | .ok resp => Json.mkObj [("result", responseJson resp)]
  | .error e => Json.mkObj [("error", Json.str e)]

end LateDelivery.Json
