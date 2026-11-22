import Mathlib

/-! Scalar minimal displacement from estimates at arbitrary comparison points.
No completeness, boundedness, or existence of a fixed point is assumed.
-/

namespace Cat0Bounds

open Filter

variable {X : Type*} [MetricSpace X]

noncomputable def minimalDisplacement (T : X → X) : ℝ :=
  sInf (Set.range fun p => dist p (T p))

theorem displacement_bddBelow (T : X → X) :
    BddBelow (Set.range fun p => dist p (T p)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, rfl⟩
  exact dist_nonneg

theorem minimalDisplacement_le (T : X → X) (p : X) :
    minimalDisplacement T ≤ dist p (T p) := by
  exact csInf_le (displacement_bddBelow T) ⟨p, rfl⟩

/-- A comparison estimate with a vanishing error at each fixed comparison
point implies convergence of the scalar residual to the infimum. -/
theorem residual_tendsto_minimalDisplacement (T : X → X) (x : ℕ → X)
    (hcomparison : ∀ p : X, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, dist (x n) (T (x n)) ≤ dist p (T p) + ε) :
    Tendsto (fun n => dist (x n) (T (x n))) atTop (nhds (minimalDisplacement T)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hnonempty : (Set.range fun p => dist p (T p)).Nonempty :=
    ⟨dist (x 0) (T (x 0)), ⟨x 0, rfl⟩⟩
  have hex : ∃ r ∈ Set.range (fun p => dist p (T p)),
      r < minimalDisplacement T + ε / 2 := by
    apply (csInf_lt_iff (displacement_bddBelow T) hnonempty).1
    change minimalDisplacement T < minimalDisplacement T + ε / 2
    linarith
  obtain ⟨r, ⟨p, rfl⟩, hp⟩ := hex
  obtain ⟨N, hN⟩ := hcomparison p (ε / 2) hhalf
  refine ⟨N, ?_⟩
  intro n hn
  have hlower := minimalDisplacement_le T (x n)
  have hupper := hN n hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- A concrete reciprocal comparison rate supplies the vanishing errors
required by `residual_tendsto_minimalDisplacement`. -/
theorem residual_tendsto_of_reciprocal_comparison (T : X → X) (u : X)
    (x : ℕ → X) (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hcomparison : ∀ p : X, ∀ n : ℕ,
      dist (x n) (T (x n)) ≤ dist p (T p) + 2 * dist u p / (b + c * n)) :
    Tendsto (fun n => dist (x n) (T (x n))) atTop (nhds (minimalDisplacement T)) := by
  apply residual_tendsto_minimalDisplacement
  intro p ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * dist u p / (c * ε))
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 2 * dist u p < (N : ℝ) * (c * ε) :=
    (div_lt_iff₀ (mul_pos hc hε)).1 hN
  have hmono := mul_le_mul_of_nonneg_right hcast (le_of_lt (mul_pos hc hε))
  have hden : 0 < b + c * (n : ℝ) := by positivity
  have herror : 2 * dist u p / (b + c * (n : ℝ)) ≤ ε := by
    apply (div_le_iff₀ hden).2
    have hpositive := mul_pos hb hε
    nlinarith only [hlarge, hmono, hpositive]
  linarith only [hcomparison p n, herror]

end Cat0Bounds
