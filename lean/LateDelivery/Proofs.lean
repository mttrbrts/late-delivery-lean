import LateDelivery.Spec

/-!
# Properties of the Late Delivery and Penalty clause

Everything here is checked by Lean's kernel when the project builds.
No `sorry`, no axioms beyond Lean's standard ones (see `#print axioms` at the end).
-/

namespace LateDelivery

/-! ## Rounding -/

/-- `ceilDiv` really is "round up": the result covers `a`, and overshoots by less than `b`. -/
theorem ceilDiv_spec (a b : Nat) (hb : 0 < b) :
    a ≤ b * ceilDiv a b ∧ b * ceilDiv a b < a + b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  generalize b * ((a + b - 1) / b) = t at *
  omega

/-- A fractional day of delay counts as a full day: the counted days cover the real
delay, and over-count it by less than one day. -/
theorem delayDays_spec (agreed effective : Int) :
    (effective - agreed).toNat ≤ msPerDay * delayDays agreed effective ∧
    msPerDay * delayDays agreed effective < (effective - agreed).toNat + msPerDay :=
  ceilDiv_spec _ _ (by decide)

theorem ceilDiv_mono {a₁ a₂ : Nat} (b : Nat) (h : a₁ ≤ a₂) : ceilDiv a₁ b ≤ ceilDiv a₂ b := by
  unfold ceilDiv; exact Nat.div_le_div_right (by omega)

/-! ## The cap -/

/-- **The penalty never exceeds the cap.** -/
theorem penalty_le_cap (c : Contract) (fm : Bool) (d v : Nat) :
    penalty c fm d v ≤ cap c v := by
  unfold penalty
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_right _ _

/-- With a cap of at most 100%, the penalty never exceeds the value of the goods. -/
theorem penalty_le_value (c : Contract) (fm : Bool) (d v : Nat) (h : c.capBp ≤ 10000) :
    penalty c fm d v ≤ v := by
  refine Nat.le_trans (penalty_le_cap c fm d v) ?_
  unfold cap
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm 10000 v]
  exact Nat.mul_le_mul_left v h

/-! ## Force majeure -/

theorem penalty_fm (c : Contract) (d v : Nat) : penalty c true d v = 0 := by
  simp [penalty]

/-! ## Monotonicity: more delay never reduces the penalty -/

theorem rawPenalty_mono (c : Contract) {d₁ d₂ : Nat} (v : Nat) (h : d₁ ≤ d₂) :
    rawPenalty c d₁ v ≤ rawPenalty c d₂ v := by
  unfold rawPenalty
  split
  · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
  · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.div_le_div_right h))
  · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (ceilDiv_mono _ h))

theorem penalty_mono (c : Contract) (fm : Bool) {d₁ d₂ : Nat} (v : Nat) (h : d₁ ≤ d₂) :
    penalty c fm d₁ v ≤ penalty c fm d₂ v := by
  have := rawPenalty_mono c v h
  unfold penalty
  split <;> omega

theorem mayTerminate_mono (c : Contract) {d₁ d₂ : Nat} (h : d₁ ≤ d₂)
    (h₁ : mayTerminate c d₁ = true) : mayTerminate c d₂ = true := by
  simp [mayTerminate] at *; omega

/-- Termination becomes available exactly when the delay exceeds the threshold. -/
theorem mayTerminate_iff (c : Contract) (d : Nat) :
    mayTerminate c d = true ↔ c.terminationDays < d := by
  simp [mayTerminate]

/-! ## Comparing interpretations of "for every N days"

Whatever a court decides the clause means, the three readings are ordered:
completed periods ≤ pro rata ≤ started periods. So the `startedPeriods` figure is a
safe upper bound on exposure and `completedPeriods` a safe lower bound. -/

section Interpretations
variable (c : Contract) (d v : Nat)

/-- Helper: `x * (d / p) ≤ x * d / p`. -/
private theorem mul_div_le (x d p : Nat) (hp : 0 < p) : x * (d / p) ≤ x * d / p := by
  rw [Nat.le_div_iff_mul_le hp, Nat.mul_assoc]
  exact Nat.mul_le_mul_left x (Nat.div_mul_le_self d p)

/-- Helper: `x * d / p ≤ x * ⌈d / p⌉`. -/
private theorem div_le_mul_ceil (x d p : Nat) (hp : 0 < p) : x * d / p ≤ x * ceilDiv d p := by
  apply Nat.div_le_of_le_mul
  have := (ceilDiv_spec d p hp).1
  calc x * d ≤ x * (p * ceilDiv d p) := Nat.mul_le_mul_left x this
    _ = p * (x * ceilDiv d p) := by
      rw [← Nat.mul_assoc, Nat.mul_comm x p, Nat.mul_assoc]

private theorem prop_eq (x d p : Nat) : x * d / (10000 * p) = x * d / p / 10000 := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm p 10000]

theorem completed_le_proportional (hp : c.valid) :
    rawPenalty { c with basis := .completedPeriods } d v ≤
    rawPenalty { c with basis := .proportional } d v := by
  simp only [rawPenalty, prop_eq]
  exact Nat.div_le_div_right (mul_div_le _ _ _ hp)

theorem proportional_le_started (hp : c.valid) :
    rawPenalty { c with basis := .proportional } d v ≤
    rawPenalty { c with basis := .startedPeriods } d v := by
  simp only [rawPenalty, prop_eq]
  exact Nat.div_le_div_right (div_le_mul_ceil _ _ _ hp)

end Interpretations

/-! ## Guarantees about the whole clause (`trigger`)

These are the statements an agent or a counterparty would rely on. -/

/-- **Maximum liability.** Whatever the dates, values or force-majeure claims, a
successful execution never yields a penalty above the cap. -/
theorem trigger_penalty_le_cap {c : Contract} {r : Request} {now : Int} {resp : Response}
    (h : trigger c r now = .ok resp) : resp.penalty ≤ cap c r.goodsValue := by
  unfold trigger at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; exact penalty_le_cap _ _ _ _

/-- If the goods arrived (or `now` is) on or before the agreed date, the clause cannot
be exercised. -/
theorem trigger_on_time_error {c : Contract} {r : Request} {now : Int}
    (h : r.deliveredAt.getD now ≤ r.agreedDelivery) :
    trigger c r now = .error invalidMsg ∨ trigger c r now = .error tooEarlyMsg := by
  unfold trigger
  split
  · exact Or.inl rfl
  · simp [h]

/-- When force majeure is both in the contract and claimed, no penalty is due. -/
theorem trigger_fm_no_penalty {c : Contract} {r : Request} {now : Int} {resp : Response}
    (hc : c.forceMajeure = true) (hr : r.forceMajeure = true)
    (h : trigger c r now = .ok resp) : resp.penalty = 0 := by
  unfold trigger at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; simp [hc, hr, penalty]

/-- A contract with a zero-length penalty period is rejected rather than producing a
penalty (a naive implementation would divide by zero). -/
theorem trigger_invalid {c : Contract} (r : Request) (now : Int) (h : ¬ c.valid) :
    trigger c r now = .error invalidMsg := by
  simp [Contract.valid] at h
  simp [trigger, h]

/-- Delivering later never reduces the penalty (same contract, value and claim). -/
theorem trigger_later_no_cheaper {c : Contract} {r : Request} {t₁ t₂ : Int}
    {resp₁ resp₂ : Response} (ht : t₁ ≤ t₂)
    (h₁ : trigger c { r with deliveredAt := some t₁ } 0 = .ok resp₁)
    (h₂ : trigger c { r with deliveredAt := some t₂ } 0 = .ok resp₂) :
    resp₁.penalty ≤ resp₂.penalty := by
  unfold trigger at h₁ h₂
  split at h₁
  · cases h₁
  · simp only [Option.getD_some] at h₁ h₂
    split at h₁
    · cases h₁
    · split at h₂
      · cases h₂
      · split at h₂
        · cases h₂
        · cases h₁; cases h₂
          apply penalty_mono
          unfold delayDays
          apply ceilDiv_mono
          omega

end LateDelivery

#print axioms LateDelivery.trigger_penalty_le_cap
#print axioms LateDelivery.trigger_later_no_cheaper
