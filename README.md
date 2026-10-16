# Late Delivery and Penalty, in Lean 4

A verified specification of the Accord Project **Late Delivery and Penalty** clause,
used three ways:

1. **Proofs.** Properties of the clause, machine-checked by Lean's kernel.
2. **Oracle.** Test vectors from the Lean model, used to check a TypeScript `logic.ts`.
3. **Runtime.** The same Lean code compiled to a native binary with a Concerto JSON boundary.

No Mathlib, so a clean build, proofs included, takes about 5 seconds.

```
lean/LateDelivery/Spec.lean    the clause as an executable Lean function (trigger)
lean/LateDelivery/Proofs.lean  the theorems
lean/LateDelivery/Json.lean    Concerto JSON in/out, exact decimals, ISO 8601 dates
lean/Main.lean                 CLI: `trigger` (runtime) and `vectors` (test oracle)
ts/logic.ts                    TypeScript logic written to the spec (the thing under test)
ts/leanRuntime.ts              TypeScript adapter that runs the Lean binary as the logic
ts/harness.ts                  differential tests: Lean vs logic.ts
examples/                      Accord's sample data.json and request.json
```

## Run it

```sh
cd lean && lake build          # checks every proof, builds lean/.lake/build/bin/latedelivery
cd .. && npm test              # 5,000 vectors; exits non-zero if logic.ts disagrees
npm run sample                 # Accord's sample contract through the Lean runtime
```

Requires Lean `v4.22.0` (pinned in `lean/lean-toolchain`) and Node 22.6 or later.

## What is proved

All in `Proofs.lean`, with no `sorry`. `#print axioms` shows only Lean's standard axioms.

| Theorem | Statement |
|---|---|
| `trigger_penalty_le_cap` | Any successful execution yields a penalty no greater than the cap. This is the maximum-liability guarantee. |
| `penalty_le_value` | With a cap of at most 100%, the penalty never exceeds the goods' value. |
| `trigger_fm_no_penalty` | If force majeure is in the contract and claimed, the penalty is 0. |
| `trigger_on_time_error` | The clause cannot be exercised on or before the agreed date. |
| `trigger_invalid` | A zero-length penalty period is rejected rather than dividing by zero. |
| `trigger_later_no_cheaper` | Later delivery never reduces the penalty. |
| `penalty_mono`, `mayTerminate_mono` | More delay never reduces the penalty or removes the termination right. |
| `mayTerminate_iff` | The termination right holds exactly when delay is greater than the threshold. |
| `delayDays_spec` | A fractional day counts as a full day, over-counting by less than one day. |
| `completed_le_proportional`, `proportional_le_started` | The three readings of "for every N days" are ordered, so they bound exposure from below and above. |

## Modelling decisions

The model is written from the clause **text**, and the questions the text leaves open
are made explicit rather than buried in code:

* **Units.** Durations are normalised to days, so "more than 2 weeks" means more
  than 14 days. Unknown units are rejected.
* **Part days.** The text says a fractional day counts as a full day, so delay rounds
  up (`delayDays_spec`).
* **Effective date.** `deliveredAt` if the goods have arrived, otherwise `now`.
* **Force majeure** removes the penalty only. The text gives no termination right.
* **Zero period.** A `penaltyDuration` of 0 is rejected as an invalid contract.
* **Accrual basis.** "For every 9 days of delay" could be pro rata, completed periods
  or started periods. This is the `accrualBasis` parameter, defaulting to pro rata.
  The ordering theorems bound the dispute.
* **Rounding.** Money rounds down to the minor unit, using exact integer arithmetic.
  The clause is silent on this.
* **"More than" versus "at least".** The text says *more than*, so the comparison is
  strict.

## Does the harness actually catch bugs?

Mutants of `logic.ts`, each run against the same 5,000 vectors:

| Mutation | Caught |
|---|---|
| `>` becomes `>=` for termination | 61 cases |
| truncate days instead of rounding up | 794 cases |
| ignore `deliveredAt` | 914 cases |
| `x / (a*b)` rewritten as `x / a / b` | 0. This one is correct: the two are equal for naturals. |

The vector generator deliberately targets boundaries: exact whole-day delays, delays
one second over, zero values, weeks units, zero periods and force majeure.

## Lean as the runtime

`latedelivery trigger` reads `{ data, request, now }` as Concerto JSON and returns
`{ result }` or `{ error }`. `ts/leanRuntime.ts` wraps it behind the same `trigger`
signature as `logic.ts`, so the code that runs is the code that was proved.
The boundary is careful:

* Decimals are read exactly from the JSON digits, never via a float. More precision
  than the model holds (for example 10.505%) is rejected, not rounded.
* Durations are normalised to days, and unknown units are rejected.
* Timestamps accept `Z` or `±HH:MM` offsets and fractional seconds.

To make this a first-class option in the template engine, you'd still need:

* A pluggable logic runtime in `TemplateArchiveProcessor`, with this JSON envelope
  as the ABI.
* State and emitted events in the envelope (this clause is stateless).
* A WASM build for browsers. Lean emits C, which Emscripten can compile, but the
  Lean runtime makes it heavier than a TypeScript function.

## Where this could go

* **A Concerto to Lean code generator** so `Contract`/`Request`/`Response` and the JSON
  boundary are generated from `model.cto`, leaving authors only the logic and theorems.
* **Theorems as template metadata.** An agent could check `trigger_penalty_le_cap`
  before accepting a contract, rather than simulating the logic.
* **Mathlib** for richer statements, such as the exact pro-rata formula over rationals,
  at the cost of build time.

## Licence

Apache License 2.0. See [LICENSE](LICENSE).
