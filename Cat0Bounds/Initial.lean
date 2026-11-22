import Cat0Bounds.Adaptive

/-! Anchored iterations with an initial point distinct from the anchor. -/

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

noncomputable def halpernFrom (G : Geometry X) (T : X → X) (u x : X) : ℕ → X
  | 0 => x
  | k + 1 => G.mix (((k : ℝ) + 1) / ((k : ℝ) + 2)) u (T (halpernFrom G T u x k))

def initialEnergy (T : X → X) (u x : X) : ℝ :=
  dist x (T x) ^ 2 - anchoredPhi T u x

noncomputable def halpernFromPotential (G : Geometry X) (T : X → X)
    (u x : X) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2 * dist (halpernFrom G T u x k) (T (halpernFrom G T u x k)) ^ 2
    - ((k : ℝ) + 1) * anchoredPhi T u (halpernFrom G T u x k)

/-- The ordinary Halpern potential decreases independently of the initial point. -/
theorem halpernFromPotential_step (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u x : X) (k : ℕ) :
    halpernFromPotential G T u x (k + 1) ≤ halpernFromPotential G T u x k := by
  let z := halpernFrom G T u x k
  let s := ((k : ℝ) + 1) / ((k : ℝ) + 2)
  let z' := G.mix s u (T z)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hden : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_iff₀ hden).2
    linarith
  have h := anchored_step G hT u z s hs0 hs1
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg ((k : ℝ) + 2))
  change ((k : ℝ) + 2) ^ 2 *
      (dist z' (T z') ^ 2 - (1 - s) * anchoredPhi T u z') ≤
    ((k : ℝ) + 2) ^ 2 *
      (s * (s * dist z (T z) ^ 2 - (1 - s) * anchoredPhi T u z)) at hm
  have hleft : ((k : ℝ) + 2) ^ 2 *
      (dist z' (T z') ^ 2 - (1 - s) * anchoredPhi T u z') =
      ((k : ℝ) + 2) ^ 2 * dist z' (T z') ^ 2
        - ((k : ℝ) + 2) * anchoredPhi T u z' := by
    dsimp [s]
    field_simp
    ring
  have hright : ((k : ℝ) + 2) ^ 2 *
      (s * (s * dist z (T z) ^ 2 - (1 - s) * anchoredPhi T u z)) =
      ((k : ℝ) + 1) ^ 2 * dist z (T z) ^ 2
        - ((k : ℝ) + 1) * anchoredPhi T u z := by
    dsimp [s]
    field_simp
    ring
  rw [hleft, hright] at hm
  simpa only [halpernFromPotential, halpernFrom, Nat.cast_add, Nat.cast_one,
    show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] using hm

theorem halpernFromPotential_le_initial (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u x : X) (N : ℕ) :
    halpernFromPotential G T u x N ≤ initialEnergy T u x := by
  induction N with
  | zero => simp [halpernFromPotential, halpernFrom, initialEnergy]
  | succ k ih => exact le_trans (halpernFromPotential_step G hT u x k) ih

/-- The square-root discriminant is nonnegative, even if the energy is negative. -/
theorem initialEnergy_discriminant_nonneg (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) {p : X} (hp : T p = p) (u x : X) :
    0 ≤ dist u p ^ 2 + initialEnergy T u x := by
  have he := endpoint G hT hp u x
  unfold initialEnergy anchoredPhi
  nlinarith only [he, sq_nonneg (dist x (T x) - dist u p)]

/-- The upper root of the scalar potential inequality. -/
theorem residual_of_initial_energy (r D E n : ℝ) (hn : 0 < n)
    (hE : 0 ≤ D ^ 2 + E) (h : n ^ 2 * r ^ 2 - 2 * D * n * r ≤ E) :
    r ≤ (D + Real.sqrt (D ^ 2 + E)) / n := by
  have hs := Real.sq_sqrt hE
  have hs0 := Real.sqrt_nonneg (D ^ 2 + E)
  have hsq : (n * r - D) ^ 2 ≤ D ^ 2 + E := by nlinarith only [h]
  have hroot : n * r - D ≤ Real.sqrt (D ^ 2 + E) := by
    nlinarith only [hsq, hs, hs0, sq_nonneg (n * r - D - Real.sqrt (D ^ 2 + E))]
  apply (le_div_iff₀ hn).2
  nlinarith only [hroot]

/-- The distinct-initial-point residual bound, with its exact initial energy. -/
theorem halpernFrom_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) {p : X} (hp : T p = p) (u x : X) (N : ℕ) :
    dist (halpernFrom G T u x N) (T (halpernFrom G T u x N)) ≤
      (dist u p + Real.sqrt (dist u p ^ 2 + initialEnergy T u x)) / ((N : ℝ) + 1) := by
  have hpot := halpernFromPotential_le_initial G hT u x N
  have he := endpoint G hT hp u (halpernFrom G T u x N)
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left he (le_of_lt hn)
  apply residual_of_initial_energy _ _ _ _ hn
    (initialEnergy_discriminant_nonneg G hT hp u x)
  unfold halpernFromPotential anchoredPhi at hpot
  nlinarith only [hpot, hm]

noncomputable def adaptiveFrom (G : Geometry X) (T : X → X) (u x : X) : ℕ → X
  | 0 => x
  | k + 1 => adaptiveStep G T u (adaptiveFrom G T u x k)

theorem adaptiveFrom_stops (G : Geometry X) (T : X → X) (u x : X) (k : ℕ)
    (hk : T (adaptiveFrom G T u x k) = adaptiveFrom G T u x k) :
    adaptiveFrom G T u x (k + 1) = adaptiveFrom G T u x k :=
  adaptiveStep_of_fixed G T u (adaptiveFrom G T u x k) hk

theorem adaptiveFrom_nonfixed_previous (G : Geometry X) (T : X → X)
    (u x : X) (k : ℕ)
    (hnext : T (adaptiveFrom G T u x (k + 1)) ≠ adaptiveFrom G T u x (k + 1)) :
    T (adaptiveFrom G T u x k) ≠ adaptiveFrom G T u x k := by
  intro hk
  have hs := adaptiveFrom_stops G T u x k hk
  exact hnext (by rw [hs, hk])

/-- Coefficient growth from any initial point with a positive initial coefficient. -/
theorem adaptiveFromCoeff_lower (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u x : X) (hφ0 : 0 < adaptiveCoeff T u x)
    (N : ℕ) (hN : T (adaptiveFrom G T u x N) ≠ adaptiveFrom G T u x N) :
    adaptiveCoeff T u x + (N : ℝ) ≤ adaptiveCoeff T u (adaptiveFrom G T u x N) := by
  induction N with
  | zero => simp [adaptiveFrom]
  | succ k ih =>
    have hk := adaptiveFrom_nonfixed_previous G T u x k hN
    have hl := ih hk
    have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hpos : 0 < adaptiveCoeff T u (adaptiveFrom G T u x k) := by
      linarith only [hl, hφ0, hkn]
    have hg := adaptiveStep_coeff_growth G hT u (adaptiveFrom G T u x k) hk hpos hN
    change adaptiveCoeff T u x + (↑(k + 1) : ℝ) ≤
      adaptiveCoeff T u (adaptiveStep G T u (adaptiveFrom G T u x k))
    push_cast
    linarith only [hl, hg]

theorem adaptiveFromCoeff_growth (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u x : X) (hφ0 : 0 < adaptiveCoeff T u x)
    (k : ℕ)
    (hnext : T (adaptiveFrom G T u x (k + 1)) ≠ adaptiveFrom G T u x (k + 1)) :
    adaptiveCoeff T u (adaptiveFrom G T u x k) + 1 ≤
      adaptiveCoeff T u (adaptiveFrom G T u x (k + 1)) := by
  have hk := adaptiveFrom_nonfixed_previous G T u x k hnext
  have hl := adaptiveFromCoeff_lower G hT u x hφ0 k hk
  apply adaptiveStep_coeff_growth G hT u (adaptiveFrom G T u x k) hk _ hnext
  have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith only [hl, hφ0, hkn]

/-- The fixed-point endpoint estimate does not need a radius assumption. -/
theorem adaptiveFrom_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) {p : X} (hp : T p = p) (u x : X)
    (hφ0 : 0 < adaptiveCoeff T u x) (N : ℕ)
    (hN : T (adaptiveFrom G T u x N) ≠ adaptiveFrom G T u x N) :
    dist (adaptiveFrom G T u x N) (T (adaptiveFrom G T u x N)) ≤
      2 * dist u p / adaptiveCoeff T u (adaptiveFrom G T u x N) := by
  have hl := adaptiveFromCoeff_lower G hT u x hφ0 N hN
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpos : 0 < adaptiveCoeff T u (adaptiveFrom G T u x N) := by
    linarith only [hl, hφ0, hNn]
  apply residual_of_sq _ _ _ dist_nonneg dist_nonneg hpos
  rw [adaptiveCoeff_mul T u (adaptiveFrom G T u x N) hN]
  exact endpoint G hT hp u (adaptiveFrom G T u x N)

/-- The initial-coefficient horizon bound, also valid after stopping. -/
theorem adaptiveFrom_horizon_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) {p : X} (hp : T p = p) (u x : X)
    (hφ0 : 0 < adaptiveCoeff T u x) (N : ℕ) :
    dist (adaptiveFrom G T u x N) (T (adaptiveFrom G T u x N)) ≤
      2 * dist u p / (adaptiveCoeff T u x + (N : ℝ)) := by
  by_cases hN : T (adaptiveFrom G T u x N) = adaptiveFrom G T u x N
  · rw [hN, dist_self]
    positivity
  · have hb := adaptiveFrom_bound G hT hp u x hφ0 N hN
    have hl := adaptiveFromCoeff_lower G hT u x hφ0 N hN
    refine le_trans hb ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl

end Cat0Bounds
