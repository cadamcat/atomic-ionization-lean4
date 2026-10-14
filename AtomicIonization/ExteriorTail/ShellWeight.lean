import OAI.Analysis.CoulombRadii.FieldAnalysis.BodyCoefficient
import OAI.Analysis.CoulombRadii.Localization.ShellIMS
import OAI.Analysis.CoulombRadii.Screening.CountMoments

/-!
# Smooth shell weights

A smooth radial weight `shellBump r` supported in the closed shell `r ≤ |y| ≤ 2r`, equal to one on
`9r/8 ≤ |y| ≤ 15r/8`, and the permutation-invariant smooth multiplier
`shellRoot r ε x = √(ε + ∑ᵢ shellBump r (xᵢ)²)` used to bias a state by its shell occupation.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb
open scoped ContDiff Topology

noncomputable section

/-- Bump equal to one on the closed unit ball, supported in the ball of radius `9/8`. -/
def innerBump : ContDiffBump (0 : Space) := ⟨1, 9 / 8, by norm_num, by norm_num⟩

/-- Bump equal to one on the closed ball of radius `15/8`, supported in the ball of radius `2`. -/
def outerBump : ContDiffBump (0 : Space) := ⟨15 / 8, 2, by norm_num, by norm_num⟩

/-- The unit shell profile: zero on `|y| ≤ 1` and on `|y| ≥ 2`, one on `9/8 ≤ |y| ≤ 15/8`. -/
def shellProfile (y : Space) : ℝ := outerBump y - innerBump y

/-- The shell profile at scale `r`. -/
def shellBump (r : ℝ) (y : Space) : ℝ := shellProfile (r⁻¹ • y)

/-- `√(ε + ∑ᵢ shellBump r (xᵢ)²)`. -/
def shellRoot (r ε : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  Real.sqrt (ε + ∑ i, (shellBump r (position x i)) ^ 2)

private lemma norm_inv_smul (r : ℝ) (hr : 0 < r) (y : Space) :
    ‖r⁻¹ • y‖ = ‖y‖ / r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), div_eq_mul_inv]
  ring

private lemma inner_le_outer (y : Space) : innerBump y ≤ outerBump y := by
  by_cases h : ‖y‖ ≤ 15 / 8
  · have ho : outerBump y = 1 := by
      apply outerBump.one_of_mem_closedBall
      have h15 : ‖y‖ ≤ 15 / 8 := by linarith
      simpa [outerBump, Metric.mem_closedBall, dist_zero_right] using h15
    rw [ho]
    exact innerBump.le_one
  · have hi : innerBump y = 0 := by
      apply innerBump.zero_of_le_dist
      have h' : 9 / 8 ≤ ‖y‖ := by nlinarith [le_of_not_ge h]
      simpa [innerBump, dist_zero_right] using h'
    rw [hi]
    exact outerBump.nonneg

theorem shellBump_nonneg (r : ℝ) (y : Space) : 0 ≤ shellBump r y := by
  exact sub_nonneg.mpr (inner_le_outer (r⁻¹ • y))

theorem shellBump_le_one (r : ℝ) (y : Space) : shellBump r y ≤ 1 := by
  unfold shellBump shellProfile
  linarith [outerBump.le_one (x := r⁻¹ • y), innerBump.nonneg (x := r⁻¹ • y)]

theorem shellBump_eq_zero {r : ℝ} (hr : 0 < r) {y : Space} (hy : ‖y‖ ≤ r ∨ 2 * r ≤ ‖y‖) :
    shellBump r y = 0 := by
  unfold shellBump shellProfile
  rcases hy with hy | hy
  · have hs : ‖r⁻¹ • y‖ ≤ 1 := by
      rw [norm_inv_smul r hr]
      apply (div_le_iff₀ hr).2
      nlinarith
    have hi : innerBump (r⁻¹ • y) = 1 := by
      apply innerBump.one_of_mem_closedBall
      simpa [innerBump, Metric.mem_closedBall, dist_zero_right] using hs
    have ho : outerBump (r⁻¹ • y) = 1 := by
      apply outerBump.one_of_mem_closedBall
      have hs' : ‖r⁻¹ • y‖ ≤ 15 / 8 := by linarith
      simpa [outerBump, Metric.mem_closedBall, dist_zero_right] using hs'
    rw [ho, hi]
    ring
  · have hs : 2 ≤ ‖r⁻¹ • y‖ := by
      rw [norm_inv_smul r hr]
      exact (le_div_iff₀ hr).2 (by nlinarith)
    have ho : outerBump (r⁻¹ • y) = 0 := by
      apply outerBump.zero_of_le_dist
      simpa [outerBump, dist_zero_right] using hs
    have hi : innerBump (r⁻¹ • y) = 0 := by
      apply innerBump.zero_of_le_dist
      have : 9 / 8 ≤ ‖r⁻¹ • y‖ := by linarith
      simpa [innerBump, dist_zero_right] using this
    rw [ho, hi]
    ring

theorem shellBump_eq_one {r : ℝ} (hr : 0 < r) {y : Space} (h₁ : 9 / 8 * r ≤ ‖y‖)
    (h₂ : ‖y‖ ≤ 15 / 8 * r) : shellBump r y = 1 := by
  unfold shellBump shellProfile
  have hs₁ : 9 / 8 ≤ ‖r⁻¹ • y‖ := by
    rw [norm_inv_smul r hr]
    exact (le_div_iff₀ hr).2 h₁
  have hs₂ : ‖r⁻¹ • y‖ ≤ 15 / 8 := by
    rw [norm_inv_smul r hr]
    exact (div_le_iff₀ hr).2 h₂
  have hi : innerBump (r⁻¹ • y) = 0 := by
    apply innerBump.zero_of_le_dist
    simpa [innerBump, dist_zero_right] using hs₁
  have ho : outerBump (r⁻¹ • y) = 1 := by
    apply outerBump.one_of_mem_closedBall
    simpa [outerBump, Metric.mem_closedBall, dist_zero_right] using hs₂
  rw [ho, hi]
  norm_num

theorem shellBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (shellBump r) := by
  unfold shellBump
  have hc : ContDiff ℝ ∞ (fun _ : Space => (r⁻¹ : ℝ)) := contDiff_const
  have hi : ContDiff ℝ ∞ (fun y : Space => y) := contDiff_id
  have hs : ContDiff ℝ ∞ (fun y : Space => (r⁻¹ : ℝ) • y) := hc.smul hi
  exact (outerBump.contDiff.sub innerBump.contDiff).comp hs

theorem fderiv_shellBump_eq_zero {r : ℝ} (hr : 0 < r) {y : Space} (hy : y ∉ imsShell 0 r) :
    fderiv ℝ (shellBump r) y = 0 := by
  have hy' : ¬ (r ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * r) := by
    simpa [imsShell, dist_zero_right] using hy
  by_cases hinner : ‖y‖ < r
  · have he : shellBump r =ᶠ[𝓝 y] (fun _ => 0) := by
      have hn : ∀ᶠ z in 𝓝 y, ‖z‖ < r :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
      filter_upwards [hn] with z hz
      exact shellBump_eq_zero hr (Or.inl hz.le)
    rw [he.fderiv_eq]
    simp
  · have houter : 2 * r < ‖y‖ := by
      have hle : r ≤ ‖y‖ := le_of_not_gt hinner
      exact lt_of_not_ge (fun h => hy' ⟨hle, h⟩)
    have he : shellBump r =ᶠ[𝓝 y] (fun _ => 0) := by
      have hn : ∀ᶠ z in 𝓝 y, 2 * r < ‖z‖ :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with z hz
      exact shellBump_eq_zero hr (Or.inr hz.le)
    rw [he.fderiv_eq]
    simp

theorem shellRoot_contDiff {r ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ContDiff ℝ ∞ (shellRoot r ε (n := n)) := by
  unfold shellRoot
  apply ContDiff.sqrt
  · apply contDiff_const.add
    apply ContDiff.sum
    intro i hi
    exact ((shellBump_contDiff r).comp (positionCLM i).contDiff).pow _
  · intro x
    apply ne_of_gt
    have hs : 0 ≤ ∑ i : Fin n, (shellBump r (position x i)) ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    linarith

theorem shellRoot_sq {r ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (x : Configuration n) :
    (shellRoot r ε x) ^ 2 = ε + ∑ i, (shellBump r (position x i)) ^ 2 := by
  unfold shellRoot
  exact Real.sq_sqrt (add_nonneg hε (Finset.sum_nonneg fun i hi => sq_nonneg _))

theorem abs_shellRoot_le {r ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (x : Configuration n) :
    |shellRoot r ε x| ≤ Real.sqrt (ε + n) := by
  unfold shellRoot
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  apply add_le_add_right
  calc
    ∑ i : Fin n, (shellBump r (position x i)) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hb0 := shellBump_nonneg r (position x i)
      have hb1 := shellBump_le_one r (position x i)
      nlinarith
    _ = n := by simp

theorem shellRoot_permute (r ε : ℝ) {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    shellRoot r ε (permute p x) = shellRoot r ε x := by
  unfold shellRoot
  simp only [position_permute]
  congr 1
  congr 1
  exact Equiv.sum_comp p (fun i : Fin n => (shellBump r (position x i)) ^ 2)

private lemma shellProfile_fderiv_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : Space, ‖fderiv ℝ shellProfile y‖ ≤ L := by
  have hcompact : HasCompactSupport shellProfile := by
    unfold shellProfile
    exact outerBump.hasCompactSupport.sub innerBump.hasCompactSupport
  obtain ⟨L, hL, hbound⟩ := hcompact.exists_bound_iteratedFDeriv
    (outerBump.contDiff.sub innerBump.contDiff) 1
  refine ⟨L, hL, fun y => ?_⟩
  simpa only [norm_iteratedFDeriv_one] using hbound 1 (by norm_num) y

private lemma shellBump_fderiv_bound {r : ℝ} (hr : 0 < r) (L : ℝ)
    (hL : ∀ y : Space, ‖fderiv ℝ shellProfile y‖ ≤ L)
    (b : Fin 3) (y : Space) :
    |fderiv ℝ (shellBump r) y (EuclideanSpace.single b 1)| ≤ L / r := by
  change |fderiv ℝ (fun z : Space => shellProfile (r⁻¹ • z)) y
    (EuclideanSpace.single b 1)| ≤ L / r
  rw [fderiv_comp_smul]
  simp only [smul_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hr)]
  have hd : |fderiv ℝ shellProfile (r⁻¹ • y) (EuclideanSpace.single b 1)| ≤ L := by
    rw [← Real.norm_eq_abs]
    simpa using (fderiv ℝ shellProfile (r⁻¹ • y)).le_of_opNorm_le (hL _) (EuclideanSpace.single b 1)
  calc
    r⁻¹ * |fderiv ℝ shellProfile (r⁻¹ • y) (EuclideanSpace.single b 1)| ≤ r⁻¹ * L :=
      mul_le_mul_of_nonneg_left hd (inv_pos.mpr hr).le
    _ = L / r := by rw [div_eq_mul_inv]; ring

private lemma shellRoot_fderiv_single {r ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (x : Configuration n) (a : Fin n × Fin 3) :
    fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1) =
      shellBump r (position x a.1) *
        fderiv ℝ (shellBump r) (position x a.1) (EuclideanSpace.single a.2 1) /
          shellRoot r ε x := by
  let q : Configuration n → ℝ := fun z => ε + ∑ i, (shellBump r (position z i)) ^ 2
  have hqcd : ContDiff ℝ ∞ q := by
    dsimp [q]
    apply contDiff_const.add
    exact ContDiff.sum (fun i hi =>
      ((shellBump_contDiff r).comp (positionCLM i).contDiff).pow 2)
  have hqdiff : DifferentiableAt ℝ q x := hqcd.differentiable (by simp) x
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, (shellBump r (position x i)) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hqpos : 0 < q x := by
    dsimp [q]
    linarith
  have hqne : q x ≠ 0 := hqpos.ne'
  have hqdir : fderiv ℝ q x (EuclideanSpace.single a 1) =
      2 * shellBump r (position x a.1) *
        fderiv ℝ (shellBump r) (position x a.1) (EuclideanSpace.single a.2 1) := by
    dsimp [q]
    rw [fderiv_const_add, fderiv_fun_sum]
    · simp only [sum_apply]
      rw [Finset.sum_eq_single a.1]
      · rw [fderiv_fun_pow 2]
        · simp only [smul_apply, smul_eq_mul]
          rw [oneBody_derivative (shellBump r) (shellBump_contDiff r) a.1 a.1 a.2 x]
          simp
        · exact ((shellBump_contDiff r).comp (positionCLM a.1).contDiff).differentiable
            (by simp) x
      · intro i hi hia
        rw [fderiv_fun_pow 2]
        · simp only [smul_apply, smul_eq_mul]
          rw [oneBody_derivative (shellBump r) (shellBump_contDiff r) i a.1 a.2 x]
          simp [hia]
        · exact ((shellBump_contDiff r).comp (positionCLM i).contDiff).differentiable
            (by simp) x
      · simp
    · intro i hi
      exact (((shellBump_contDiff r).comp (positionCLM i).contDiff).pow 2).differentiable
        (by simp) x
  have hsqrt : fderiv ℝ (fun z : Configuration n => Real.sqrt (q z)) x =
      (1 / (2 * Real.sqrt (q x))) • fderiv ℝ q x := fderiv_sqrt hqdiff hqne
  have hrootpos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hqpos
  have hroot : shellRoot r ε (n := n) = fun z => Real.sqrt (q z) := by
    rfl
  rw [hroot, hsqrt]
  simp only [smul_apply, smul_eq_mul, hqdir, q]
  field_simp [hrootpos.ne']

private lemma shellRoot_fderiv_partial_bound {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (L : ℝ)
    (hprofile : ∀ y : Space, ‖fderiv ℝ shellProfile y‖ ≤ L)
    {n : ℕ} (x : Configuration n) (a : Fin n × Fin 3) :
    |fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)| ≤ L / r := by
  rw [shellRoot_fderiv_single hε x a]
  let χ := shellBump r (position x a.1)
  have hχ0 : 0 ≤ χ := shellBump_nonneg r (position x a.1)
  have hroot0 : 0 ≤ shellRoot r ε x := Real.sqrt_nonneg _
  have hrootpos : 0 < shellRoot r ε x := by
    unfold shellRoot
    apply Real.sqrt_pos.2
    have hs : 0 ≤ ∑ i : Fin n, (shellBump r (position x i)) ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    linarith
  have hχsq : χ ^ 2 ≤ (shellRoot r ε x) ^ 2 := by
    rw [shellRoot_sq hε.le]
    dsimp [χ]
    calc
      (shellBump r (position x a.1)) ^ 2 ≤
          ∑ i : Fin n, (shellBump r (position x i)) ^ 2 :=
        Finset.single_le_sum (fun i hi => sq_nonneg (shellBump r (position x i)))
          (Finset.mem_univ a.1)
      _ ≤ ε + ∑ i : Fin n, (shellBump r (position x i)) ^ 2 := by linarith
  have hχroot : χ ≤ shellRoot r ε x :=
    (sq_le_sq₀ hχ0 hroot0).1 hχsq
  have hD : |fderiv ℝ (shellBump r) (position x a.1)
      (EuclideanSpace.single a.2 1)| ≤ L / r :=
    shellBump_fderiv_bound hr L hprofile a.2 (position x a.1)
  rw [abs_div, abs_mul, abs_of_nonneg hχ0, abs_of_pos hrootpos]
  apply (div_le_iff₀ hrootpos).2
  calc
    χ * |fderiv ℝ (shellBump r) (position x a.1) (EuclideanSpace.single a.2 1)| ≤
        shellRoot r ε x * |fderiv ℝ (shellBump r) (position x a.1) (EuclideanSpace.single a.2 1)| :=
      mul_le_mul_of_nonneg_right hχroot (abs_nonneg _)
    _ ≤ shellRoot r ε x * (L / r) := mul_le_mul_of_nonneg_left hD hroot0
    _ = (L / r) * shellRoot r ε x := by ring

/-- Derivative bounds at scale `r`, with one constant `L` for the bump and the root. -/
theorem shell_derivative_bounds : ∃ L : ℝ, 0 ≤ L ∧
    (∀ {r : ℝ}, 0 < r → ∀ (b : Fin 3) (y : Space),
      |fderiv ℝ (shellBump r) y (EuclideanSpace.single b 1)| ≤ L / r) ∧
    (∀ {r ε : ℝ}, 0 < r → 0 < ε → ∀ {n : ℕ} (x : Configuration n) (a : Fin n × Fin 3),
      |fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)| ≤ L / r) ∧
    (∀ {r ε : ℝ}, 0 < r → 0 < ε → ∀ {n : ℕ} (x : Configuration n),
      ∑ a : Fin n × Fin 3, (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 ≤
        3 * (L / r) ^ 2 * localCount (imsShell 0 r) x) := by
  obtain ⟨L, hL, hprofile⟩ := shellProfile_fderiv_bound
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro r hr b y
    exact shellBump_fderiv_bound hr L hprofile b y
  · intro r ε hr hε n x a
    exact shellRoot_fderiv_partial_bound hr hε L hprofile x a
  · intro r ε hr hε n x
    calc
      ∑ a : Fin n × Fin 3,
          (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 ≤
          ∑ a : Fin n × Fin 3, (L / r) ^ 2 *
            (imsShell 0 r).indicator (fun _ => (1 : ℝ)) (position x a.1) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hmem : position x a.1 ∈ imsShell 0 r
        · rw [Set.indicator_of_mem hmem]
          simp only [mul_one]
          have hbound := shellRoot_fderiv_partial_bound hr hε L hprofile x a
          have hsquare :=
            (sq_le_sq₀ (abs_nonneg _) (div_nonneg hL hr.le)).2 hbound
          simpa only [sq_abs] using hsquare
        · have hzero := fderiv_shellBump_eq_zero hr hmem
          rw [shellRoot_fderiv_single hε x a, hzero]
          simp [Set.indicator_of_notMem hmem]
      _ = ∑ i : Fin n, ∑ b : Fin 3, (L / r) ^ 2 *
            (imsShell 0 r).indicator (fun _ => (1 : ℝ)) (position x i) := by
        rw [Fintype.sum_prod_type]
      _ = 3 * (L / r) ^ 2 * localCount (imsShell 0 r) x := by
        unfold localCount
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

end

end AtomicIonization.ExteriorTail
