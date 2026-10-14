import OAI.Analysis.CoulombRadii.FormDomain.ExplicitMultiplyGradient
import OAI.Analysis.CoulombRadii.Localization.RadialCut

/-!
# Symmetric core cuts around a center

`coreProduct y r` is the product over all particles of the one-particle cut that vanishes on the
closed ball of radius `r` about `y` and equals one outside the ball of radius `2r`. It is a
symmetric smooth multiplier. Writing the one-particle cut as the cosine of a cut angle gives the
key pointwise bound: the squared gradient of the product is at most `1 - F²` times a constant
times the number of particles near `y`. The complementary multiplier `√(1 + ε - F²)` is then
again a symmetric smooth multiplier with squared gradient controlled by the near count.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory
open Filter
open scoped ContDiff Topology

noncomputable section

/-- One-particle core cut: zero on the closed ball of radius `r` about `y`, one outside the ball of
radius `2r`. -/
def coreCut (y : Position) (r : ℝ) (z : Position) : ℝ := Coulomb.radialCut y r 1 z

/-- The symmetric product of the one-particle core cuts. -/
def coreProduct (y : Position) (r : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  ∏ i, coreCut y r (x i)

/-- The number of particles in the closed ball of radius `2r` about `y`. -/
def nearCount (y : Position) (r : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i, (Metric.closedBall y (2 * r)).indicator (fun _ => (1 : ℝ)) (x i)

/-- The gradient constant of the core cut at scale `r`. -/
def cutGradientConstant (r : ℝ) : ℝ := 3 * (Coulomb.radialCutCoefficient / r) ^ 2

/-- The complementary loss multiplier `√(1 + ε - F²)`. -/
def lossMultiplier (y : Position) (r ε : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  Real.sqrt (1 + ε - coreProduct y r x ^ 2)

lemma coreCut_nonneg (y : Position) (r : ℝ) (z : Position) :
    0 ≤ coreCut y r z := by
  have hs : 0 ≤ Coulomb.cutSeed (r⁻¹ • (z-y)) := Real.smoothTransition.nonneg _
  have hs' : Coulomb.cutSeed (r⁻¹ • (z-y)) ≤ 1 := Real.smoothTransition.le_one _
  have ha : Coulomb.cutAngle y r z ∈ Set.Icc 0 (Real.pi/2) := by
    rw [Coulomb.cutAngle]
    constructor
    · exact mul_nonneg (by positivity) hs
    · calc
        (Real.pi/2) * Coulomb.cutSeed (r⁻¹ • (z-y)) ≤ (Real.pi/2) * 1 :=
          mul_le_mul_of_nonneg_left hs' (by positivity)
        _ = Real.pi/2 := by ring
  unfold coreCut Coulomb.radialCut
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩

lemma coreCut_le_one (y : Position) (r : ℝ) (z : Position) :
    coreCut y r z ≤ 1 := by
  unfold coreCut Coulomb.radialCut
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  exact Real.cos_le_one _

lemma coreProduct_fderiv {n : ℕ} (y : Position) (r : ℝ)
    (x : Configuration n) (i : Fin n) (a : Fin 3) :
    fderiv ℝ (coreProduct y r) x (coordinateDirection i a) =
      fderiv ℝ (coreCut y r) (x i) (EuclideanSpace.single a 1) *
        ∏ j ∈ Finset.univ.erase i, coreCut y r (x j) := by
  have hEval (j : Fin n) : HasFDerivAt (fun w : Configuration n => w j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Position) j) x := by
    change HasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Position) j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Position) j) x
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Position) j).hasFDerivAt
  have hd (j : Fin n) : DifferentiableAt ℝ
      (fun w : Configuration n => coreCut y r (w j)) x :=
    (((Coulomb.radialCut_smooth y r 1).differentiable (by simp) (x j)).hasFDerivAt.comp x
      (hEval j)).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun w : Configuration n => coreCut y r (w j)) x =
      (fderiv ℝ (coreCut y r) (x j)).comp (ContinuousLinearMap.proj j) :=
    (((Coulomb.radialCut_smooth y r 1).differentiable (by simp) (x j)).hasFDerivAt.comp x
      (hEval j)).fderiv
  have hdir (j : Fin n) :
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Position) j)
        (coordinateDirection i a) =
        if j = i then EuclideanSpace.single a 1 else 0 := by
    by_cases h : j = i
    · subst j
      simp [coordinateDirection]
    · simp [coordinateDirection, h]
  unfold coreProduct
  rw [fderiv_finsetProd (fun j (_ : j ∈ Finset.univ) => hd j), sum_apply]
  simp only [smul_apply, smul_eq_mul, he, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · simp [hdir]
    ring
  · intro j hj hji
    have hne : j ≠ i := fun h => hji h
    simp [hdir, hne]
  · simp

lemma coreCut_fderiv_zero_inner (y : Position) {r : ℝ} (hr : 0 < r)
    (z : Position) (hz : ‖z-y‖ < r) : fderiv ℝ (coreCut y r) z = 0 := by
  have he : coreCut y r =ᶠ[𝓝 z] fun _ : Position => 0 := by
    have hh : ∀ᶠ w in 𝓝 z, ‖w-y‖ < r :=
      (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds
        (show z ∈ {w : Position | ‖w-y‖ < r} from hz)
    filter_upwards [hh] with w hw
    exact Coulomb.radialCut_core_zero y hr w hw.le
  calc
    fderiv ℝ (coreCut y r) z = fderiv ℝ (fun _ : Position => (0 : ℝ)) z := he.fderiv_eq
    _ = 0 := fderiv_const_apply _

theorem coreProduct_multiplier {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r) :
    SmoothMultiplier (coreProduct (n := n) y r) := by
  refine ⟨?_, ?_, ⟨1, ?_⟩, ?_⟩
  · unfold coreProduct
    apply contDiff_prod
    intro i hi
    exact (Coulomb.radialCut_smooth y r 1).comp
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Position).contDiff
  · intro p x
    unfold coreProduct
    simp only [Function.comp_apply]
    exact Equiv.prod_comp p (fun i => coreCut y r (x i))
  · intro x
    have h0 : 0 ≤ coreProduct y r x := by
      unfold coreProduct
      exact Finset.prod_nonneg fun i hi => coreCut_nonneg y r (x i)
    have h1 : coreProduct y r x ≤ 1 := by
      unfold coreProduct
      exact Finset.prod_le_one₀ (fun i hi => coreCut_nonneg y r (x i))
        (fun i hi => coreCut_le_one y r (x i))
    rw [abs_of_nonneg h0]
    exact h1
  · intro i a
    refine ⟨Coulomb.radialCutCoefficient/r, fun x => ?_⟩
    rw [coreProduct_fderiv]
    rw [abs_mul]
    calc
      |fderiv ℝ (coreCut y r) (x i) (EuclideanSpace.single a 1)| *
          |∏ j ∈ Finset.univ.erase i, coreCut y r (x j)| ≤
        (Coulomb.radialCutCoefficient/r) * 1 :=
          mul_le_mul (by
            change |fderiv ℝ (Coulomb.radialCut y r 1) (x i)
              (EuclideanSpace.single a 1)| ≤ _
            exact Coulomb.radialCut_derivative_bound y hr 1 a (x i))
            (Coulomb.abs_prod_le_one _ _ (fun j hj => by
              rw [abs_of_nonneg (coreCut_nonneg y r (x j))]
              exact coreCut_le_one y r (x j)))
            (abs_nonneg _) (div_nonneg Coulomb.radialCutCoefficient_pos.le hr.le)
      _ = Coulomb.radialCutCoefficient/r := by ring

theorem coreProduct_nonneg {n : ℕ} (y : Position) (r : ℝ) (x : Configuration n) :
    0 ≤ coreProduct y r x := by
  unfold coreProduct
  exact Finset.prod_nonneg fun i hi => coreCut_nonneg y r (x i)

theorem coreProduct_le_one {n : ℕ} (y : Position) (r : ℝ) (x : Configuration n) :
    coreProduct y r x ≤ 1 := by
  unfold coreProduct
  exact Finset.prod_le_one₀ (fun i hi => coreCut_nonneg y r (x i))
    (fun i hi => coreCut_le_one y r (x i))

theorem coreProduct_support {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r) {x : Configuration n}
    (hx : coreProduct y r x ≠ 0) (i : Fin n) : r < ‖x i - y‖ := by
  by_contra h
  have hdist : ‖x i - y‖ ≤ r := le_of_not_gt h
  have hzero : coreCut y r (x i) = 0 := by
    simpa [coreCut] using Coulomb.radialCut_core_zero y hr (x i) hdist
  have hprod : coreProduct y r x = 0 := by
    unfold coreProduct
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  exact hx hprod

theorem coreProduct_fderiv_support {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r)
    {x : Configuration n} {i : Fin n} {a : Fin 3}
    (hx : fderiv ℝ (coreProduct y r) x (coordinateDirection i a) ≠ 0) (j : Fin n) :
    r ≤ ‖x j - y‖ := by
  by_cases hji : j = i
  · subst j
    by_contra hlt
    have hinner : ‖x i - y‖ < r := lt_of_not_ge hlt
    have hzero := coreCut_fderiv_zero_inner y hr (x i) hinner
    have hD : fderiv ℝ (coreProduct y r) x (coordinateDirection i a) = 0 := by
      rw [coreProduct_fderiv, hzero]
      simp
    exact hx hD
  · by_contra hlt
    have hinner : ‖x j - y‖ < r := lt_of_not_ge hlt
    have hzero : coreCut y r (x j) = 0 := by
      simpa [coreCut] using
        Coulomb.radialCut_core_zero y hr (x j) (le_of_lt hinner)
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
    have hprod : (∏ k ∈ Finset.univ.erase i, coreCut y r (x k)) = 0 :=
      Finset.prod_eq_zero hjmem hzero
    have hD : fderiv ℝ (coreProduct y r) x (coordinateDirection i a) = 0 := by
      rw [coreProduct_fderiv, hprod]
      simp
    exact hx hD

theorem one_sub_coreProduct_sq_le {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r)
    (x : Configuration n) : 1 - coreProduct y r x ^ 2 ≤ nearCount y r x := by
  classical
  by_cases hnear : ∃ i, x i ∈ Metric.closedBall y (2*r)
  · obtain ⟨i, hi⟩ := hnear
    have hcount : 1 ≤ nearCount y r x := by
      unfold nearCount
      have hnonneg (j : Fin n) :
          0 ≤ (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x j) := by
        change 0 ≤ (if x j ∈ Metric.closedBall y (2*r) then (1:ℝ) else 0)
        split_ifs <;> norm_num
      calc
        1 = (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i) := by
          simp [hi]
        _ ≤ ∑ j : Fin n, (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x j) :=
          Finset.single_le_sum (f := fun j =>
            (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x j))
            (fun j hj => hnonneg j) (Finset.mem_univ i)
    have hF := coreProduct_nonneg y r x
    nlinarith [sq_nonneg (coreProduct y r x)]
  · have hnot : ∀ i, x i ∉ Metric.closedBall y (2*r) := by
      intro i hi
      exact hnear ⟨i, hi⟩
    have hcount : nearCount y r x = 0 := by
      unfold nearCount
      apply Finset.sum_eq_zero
      intro i hi
      simp [hnot i]
    have hcut (i : Fin n) : coreCut y r (x i) = 1 := by
      have hout : 2*r ≤ ‖x i-y‖ := by
        have hlt : 2*r < dist (x i) y := by
          have hnotdist : ¬ dist (x i) y ≤ 2*r := by
            simpa only [Metric.mem_closedBall] using hnot i
          exact lt_of_not_ge hnotdist
        simpa only [dist_eq_norm] using hlt.le
      have hscaled : 2 ≤ ‖r⁻¹ • (x i-y)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact (le_inv_mul_iff₀ hr).2 (by simpa only [mul_comm] using hout)
      simp [coreCut, Coulomb.radialCut, Coulomb.cutAngle,
        Coulomb.cutSeed_zero _ hscaled]
    have hF : coreProduct y r x = 1 := by
      unfold coreProduct
      simp [hcut]
    rw [hF, hcount]
    norm_num

lemma coreCut_fderiv_sq_bound (y : Position) {r : ℝ} (hr : 0 < r)
    (z : Position) (a : Fin 3) :
    (fderiv ℝ (coreCut y r) z (EuclideanSpace.single a 1)) ^ 2 ≤
      (1 - coreCut y r z ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 := by
  let v : Position := EuclideanSpace.single a 1
  have hangle : |fderiv ℝ (Coulomb.cutAngle y r) z v| ≤ Coulomb.radialCutCoefficient/r := by
    rw [Coulomb.cutAngle_fderiv, abs_mul,
      abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hr))]
    have H := ((fderiv ℝ Coulomb.cutSeed (r⁻¹ • (z-y))).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (Coulomb.norm_cutSeed_derivative _) (norm_nonneg _))
    simp [v, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at H
    calc
      _ ≤ (Real.pi/2)*r⁻¹*Coulomb.cutSeedDerivativeBound :=
        mul_le_mul_of_nonneg_left H (by positivity)
      _ = Coulomb.radialCutCoefficient/r := by
        unfold Coulomb.radialCutCoefficient
        ring
  have hder : fderiv ℝ (coreCut y r) z v =
      -(Real.sin (Coulomb.cutAngle y r z)) *
        fderiv ℝ (Coulomb.cutAngle y r) z v := by
    change fderiv ℝ (Coulomb.radialCut y r 1) z v = _
    unfold Coulomb.radialCut
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [fderiv_cos ((Coulomb.cutAngle_smooth y r).differentiable (by simp) z)]
    simp only [smul_apply, smul_eq_mul]
  have hcut : coreCut y r z = Real.cos (Coulomb.cutAngle y r z) := by
    simp [coreCut, Coulomb.radialCut]
  have hsin : Real.sin (Coulomb.cutAngle y r z) ^ 2 = 1 - coreCut y r z ^ 2 := by
    rw [hcut]
    nlinarith [Real.sin_sq_add_cos_sq (Coulomb.cutAngle y r z)]
  have hangleSq : (fderiv ℝ (Coulomb.cutAngle y r) z v) ^ 2 ≤
      (Coulomb.radialCutCoefficient/r) ^ 2 := by
    rcases abs_le.mp hangle with ⟨hlo, hhi⟩
    nlinarith
  calc
    (fderiv ℝ (coreCut y r) z (EuclideanSpace.single a 1)) ^ 2 =
        (Real.sin (Coulomb.cutAngle y r z) ^ 2) *
          (fderiv ℝ (Coulomb.cutAngle y r) z v) ^ 2 := by
      simp only [v] at hder ⊢
      rw [hder]
      ring
    _ ≤ (Real.sin (Coulomb.cutAngle y r z) ^ 2) *
          (Coulomb.radialCutCoefficient/r) ^ 2 :=
      mul_le_mul_of_nonneg_left hangleSq (sq_nonneg _)
    _ = (1 - coreCut y r z ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 := by
      rw [hsin]

lemma coreProduct_partial_sq_bound {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r)
    (x : Configuration n) (i : Fin n) (a : Fin 3) :
    (fderiv ℝ (coreProduct y r) x (coordinateDirection i a)) ^ 2 ≤
      ((1 - coreProduct y r x ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2) *
        (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i) := by
  classical
  by_cases hnear : x i ∈ Metric.closedBall y (2*r)
  · have hc : 0 ≤ coreCut y r (x i) := coreCut_nonneg y r (x i)
    have hc1 : coreCut y r (x i) ≤ 1 := coreCut_le_one y r (x i)
    have hc2 : coreCut y r (x i) ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hc (by norm_num)).2 hc1
    let c : ℝ := coreCut y r (x i)
    let p : ℝ := ∏ j ∈ Finset.univ.erase i, coreCut y r (x j)
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact Finset.prod_nonneg fun j hj => coreCut_nonneg y r (x j)
    have hp1 : p ≤ 1 := by
      dsimp [p]
      exact Finset.prod_le_one₀
        (fun j hj => coreCut_nonneg y r (x j))
        (fun j hj => coreCut_le_one y r (x j))
    have hp2 : p ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hp0 (by norm_num)).2 hp1
    have hF : coreProduct y r x = c * p := by
      dsimp [c, p]
      unfold coreProduct
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have hCF : 1 - c ^ 2 ≤ 1 - coreProduct y r x ^ 2 := by
      rw [hF]
      have hcp : c ^ 2 * p ^ 2 ≤ c ^ 2 := by
        calc
          c ^ 2 * p ^ 2 ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hp2 (sq_nonneg c)
          _ = c ^ 2 := by ring
      nlinarith
    have hD :
        (fderiv ℝ (coreCut y r) (x i) (EuclideanSpace.single a 1)) ^ 2 ≤
          (1 - c ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 := by
      simpa [c] using coreCut_fderiv_sq_bound y hr (x i) a
    have hcoeff : 0 ≤ (1 - c ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg _)
    simp only [Set.indicator_of_mem hnear, mul_one]
    rw [coreProduct_fderiv]
    change (fderiv ℝ (coreCut y r) (x i) (EuclideanSpace.single a 1) * p) ^ 2 ≤ _
    calc
      _ = (fderiv ℝ (coreCut y r) (x i) (EuclideanSpace.single a 1)) ^ 2 * p ^ 2 := by
        rw [mul_pow]
      _ ≤ ((1 - c ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2) * p ^ 2 :=
        mul_le_mul_of_nonneg_right hD (sq_nonneg p)
      _ ≤ (1 - c ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 := by
        calc
          _ ≤ ((1 - c ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hp2 hcoeff
          _ = _ := by ring
      _ ≤ (1 - coreProduct y r x ^ 2) * (Coulomb.radialCutCoefficient/r) ^ 2 :=
        mul_le_mul_of_nonneg_right hCF (sq_nonneg _)
  · have hlt : 2*r < ‖x i-y‖ := by
      have hnotdist : ¬ dist (x i) y ≤ 2*r := by
        simpa only [Metric.mem_closedBall] using hnear
      simpa only [dist_eq_norm] using lt_of_not_ge hnotdist
    have hzero : fderiv ℝ (coreCut y r) (x i) = 0 := by
      change fderiv ℝ (Coulomb.radialCut y r 1) (x i) = 0
      exact Coulomb.radialCut_fderiv_zero y hr 1 (x i) hlt
    have hder : fderiv ℝ (coreProduct y r) x (coordinateDirection i a) = 0 := by
      rw [coreProduct_fderiv, hzero]
      simp
    rw [hder, Set.indicator_of_notMem hnear]
    simp

theorem coreProduct_gradient_bound {n : ℕ} (y : Position) {r : ℝ} (hr : 0 < r)
    (x : Configuration n) :
    (∑ i : Fin n, ∑ a : Fin 3, (fderiv ℝ (coreProduct y r) x (coordinateDirection i a)) ^ 2) ≤
      (1 - coreProduct y r x ^ 2) * (cutGradientConstant r * nearCount y r x) := by
  classical
  let D : ℝ := Coulomb.radialCutCoefficient/r
  have hpartial (i : Fin n) (a : Fin 3) := coreProduct_partial_sq_bound y hr x i a
  calc
    (∑ i : Fin n, ∑ a : Fin 3,
        (fderiv ℝ (coreProduct y r) x (coordinateDirection i a)) ^ 2) ≤
      ∑ i : Fin n, ∑ a : Fin 3,
        ((1 - coreProduct y r x ^ 2) * D ^ 2) *
          (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro a ha
        simpa [D, mul_assoc] using hpartial i a
    _ = (1 - coreProduct y r x ^ 2) *
          (cutGradientConstant r * nearCount y r x) := by
        have hinner (i : Fin n) :
            (∑ a : Fin 3, ((1 - coreProduct y r x ^ 2) * D ^ 2) *
              (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i)) =
            3 * ((1 - coreProduct y r x ^ 2) * D ^ 2) *
              (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        simp_rw [hinner]
        rw [← Finset.mul_sum]
        rw [show (∑ i : Fin n,
          (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i)) =
            nearCount y r x by rfl]
        simp [cutGradientConstant, D]
        ring

theorem lossMultiplier_multiplier {n : ℕ} (y : Position) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    SmoothMultiplier (lossMultiplier (n := n) y r ε) := by
  let F : Configuration n → ℝ := coreProduct y r
  let q : Configuration n → ℝ := fun x => 1 + ε - F x ^ 2
  let hcore := coreProduct_multiplier (n := n) y hr
  have hFsq (x : Configuration n) : F x ^ 2 ≤ 1 := by
    simpa [F] using (sq_le_sq₀ (coreProduct_nonneg y r x) (by norm_num)).2
      (coreProduct_le_one y r x)
  have hqpos (x : Configuration n) : 0 < q x := by
    dsimp [q]
    linarith [hFsq x]
  have hq_smooth : ContDiff ℝ ∞ q := by
    dsimp [q]
    exact contDiff_const.sub (hcore.smooth.pow 2)
  have hFdiff (x : Configuration n) : DifferentiableAt ℝ F x :=
    (hcore.smooth.differentiable (by simp) x)
  have hsqderiv (x : Configuration n) :
      fderiv ℝ (fun z : Configuration n => F z ^ 2) x =
        (2 * F x) • fderiv ℝ F x := by
    simp only [pow_two]
    change fderiv ℝ (F * F) x = _
    rw [fderiv_mul (hFdiff x) (hFdiff x)]
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hqderiv (x : Configuration n) (v : Configuration n) :
      fderiv ℝ q x v = -2 * F x * fderiv ℝ F x v := by
    dsimp [q]
    rw [fderiv_const_sub, hsqderiv x]
    simp only [neg_apply, smul_apply, smul_eq_mul]
    ring
  have htheta_deriv (x : Configuration n) (i : Fin n) (a : Fin 3) :
      fderiv ℝ (lossMultiplier y r ε) x (coordinateDirection i a) =
        -(F x * fderiv ℝ F x (coordinateDirection i a)) / Real.sqrt (q x) := by
    have hqdiff : DifferentiableAt ℝ q x :=
      hq_smooth.differentiable (by simp) x
    change fderiv ℝ (fun z : Configuration n => Real.sqrt (q z)) x
      (coordinateDirection i a) = _
    rw [fderiv_sqrt hqdiff (ne_of_gt (hqpos x))]
    simp only [smul_apply, smul_eq_mul]
    rw [hqderiv x (coordinateDirection i a)]
    have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 (hqpos x)).ne'
    field_simp [hs]
  have hsmooth : ContDiff ℝ ∞ (fun x : Configuration n => Real.sqrt (q x)) :=
    hq_smooth.sqrt (fun x => ne_of_gt (hqpos x))
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun x : Configuration n => Real.sqrt (q x))
    exact hsmooth
  · intro p x
    change Real.sqrt (1 + ε - coreProduct y r (x ∘ p) ^ 2) =
      Real.sqrt (1 + ε - coreProduct y r x ^ 2)
    rw [hcore.symmetric p x]
  · refine ⟨Real.sqrt (1 + ε), fun x => ?_⟩
    have harg : 1 + ε - coreProduct y r x ^ 2 ≤ 1 + ε := by
      nlinarith [sq_nonneg (coreProduct y r x)]
    change |Real.sqrt (q x)| ≤ Real.sqrt (1 + ε)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt harg
  · intro i a
    obtain ⟨B, hB⟩ := hcore.derivative_bounded i a
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    refine ⟨B / Real.sqrt ε, fun x => ?_⟩
    have hrootPos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
    have hrootε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hqε : ε ≤ q x := by
      dsimp [q]
      linarith [hFsq x]
    have hroot : Real.sqrt ε ≤ Real.sqrt (q x) := Real.sqrt_le_sqrt hqε
    have hFabs : |F x| ≤ 1 := by
      rw [abs_of_nonneg (by simpa [F] using coreProduct_nonneg y r x)]
      exact coreProduct_le_one y r x
    have hderiv_abs : |fderiv ℝ F x (coordinateDirection i a)| ≤ B := by
      simpa [F] using hB x
    have hnum : |F x| * |fderiv ℝ F x (coordinateDirection i a)| ≤ B := by
      calc
        _ ≤ 1 * B := mul_le_mul hFabs hderiv_abs (abs_nonneg _) (by norm_num)
        _ = B := by ring
    have hfrac :
        (|F x| * |fderiv ℝ F x (coordinateDirection i a)|) / Real.sqrt (q x) ≤
          B / Real.sqrt ε := by
      calc
        _ ≤ B / Real.sqrt (q x) := div_le_div_of_nonneg_right hnum hrootPos.le
        _ ≤ B / Real.sqrt ε := div_le_div_of_nonneg_left hB0 hrootε hroot
    rw [htheta_deriv x i a, abs_div, abs_neg, abs_mul, abs_of_pos hrootPos]
    exact hfrac

theorem lossMultiplier_sq {n : ℕ} (y : Position) (r : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (x : Configuration n) : lossMultiplier y r ε x ^ 2 = 1 + ε - coreProduct y r x ^ 2 := by
  have hF : coreProduct y r x ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ (coreProduct_nonneg y r x) (by norm_num)).2
      (coreProduct_le_one y r x)
  have harg : 0 ≤ 1 + ε - coreProduct y r x ^ 2 := by linarith
  simp only [lossMultiplier]
  exact Real.sq_sqrt harg

theorem lossMultiplier_gradient_bound {n : ℕ} (y : Position) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (x : Configuration n) :
    (∑ i : Fin n, ∑ a : Fin 3, (fderiv ℝ (lossMultiplier y r ε) x (coordinateDirection i a)) ^ 2) ≤
      cutGradientConstant r * nearCount y r x := by
  let F : Configuration n → ℝ := coreProduct y r
  let q : Configuration n → ℝ := fun z => 1 + ε - F z ^ 2
  have hFsq (z : Configuration n) : F z ^ 2 ≤ 1 := by
    simpa [F] using (sq_le_sq₀ (coreProduct_nonneg y r z) (by norm_num)).2
      (coreProduct_le_one y r z)
  have hqpos (z : Configuration n) : 0 < q z := by
    dsimp [q]
    linarith [hFsq z]
  have hq_smooth : ContDiff ℝ ∞ q := by
    dsimp [q]
    exact contDiff_const.sub ((coreProduct_multiplier (n := n) y hr).smooth.pow 2)
  have hFdiff (z : Configuration n) : DifferentiableAt ℝ F z :=
    (coreProduct_multiplier (n := n) y hr).smooth.differentiable (by simp) z
  have hsqderiv (z : Configuration n) :
      fderiv ℝ (fun w : Configuration n => F w ^ 2) z =
        (2 * F z) • fderiv ℝ F z := by
    simp only [pow_two]
    change fderiv ℝ (F * F) z = _
    rw [fderiv_mul (hFdiff z) (hFdiff z)]
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hqderiv (z : Configuration n) (v : Configuration n) :
      fderiv ℝ q z v = -2 * F z * fderiv ℝ F z v := by
    dsimp [q]
    rw [fderiv_const_sub, hsqderiv z]
    simp only [neg_apply, smul_apply, smul_eq_mul]
    ring
  have htheta_deriv (i : Fin n) (a : Fin 3) :
      fderiv ℝ (lossMultiplier y r ε) x (coordinateDirection i a) =
        -(F x * fderiv ℝ F x (coordinateDirection i a)) / Real.sqrt (q x) := by
    have hqdiff : DifferentiableAt ℝ q x := hq_smooth.differentiable (by simp) x
    change fderiv ℝ (fun z : Configuration n => Real.sqrt (q z)) x
      (coordinateDirection i a) = _
    rw [fderiv_sqrt hqdiff (ne_of_gt (hqpos x))]
    simp only [smul_apply, smul_eq_mul]
    rw [hqderiv x (coordinateDirection i a)]
    have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 (hqpos x)).ne'
    field_simp [hs]
  have hterm (i : Fin n) (a : Fin 3) :
      (fderiv ℝ (lossMultiplier y r ε) x (coordinateDirection i a)) ^ 2 =
        (F x ^ 2 * (fderiv ℝ F x (coordinateDirection i a)) ^ 2) / q x := by
    rw [htheta_deriv, div_pow, Real.sq_sqrt (le_of_lt (hqpos x))]
    simp only [neg_sq]
    ring
  have hsum :
      (∑ i : Fin n, ∑ a : Fin 3,
        (fderiv ℝ (lossMultiplier y r ε) x (coordinateDirection i a)) ^ 2) =
        (F x ^ 2 / q x) *
          ∑ i : Fin n, ∑ a : Fin 3,
            (fderiv ℝ F x (coordinateDirection i a)) ^ 2 := by
    calc
      _ = ∑ i : Fin n, ∑ a : Fin 3,
            (F x ^ 2 * (fderiv ℝ F x (coordinateDirection i a)) ^ 2) / q x := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro a ha
          exact hterm i a
      _ = _ := by
          have hfactor (i : Fin n) (a : Fin 3) :
              (F x ^ 2 * (fderiv ℝ F x (coordinateDirection i a)) ^ 2) / q x =
                (F x ^ 2 / q x) * (fderiv ℝ F x (coordinateDirection i a)) ^ 2 := by
            ring
          simp_rw [hfactor]
          simp only [← Finset.mul_sum]
  have hnear_nonneg : 0 ≤ nearCount y r x := by
    classical
    unfold nearCount
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : x i ∈ Metric.closedBall y (2*r) <;> simp [h]
  have hK : 0 ≤ cutGradientConstant r := by
    unfold cutGradientConstant
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hratio : (F x ^ 2 / q x) * (1 - F x ^ 2) ≤ 1 := by
    have hnum : F x ^ 2 * (1 - F x ^ 2) ≤ q x := by
      dsimp [q]
      nlinarith [sq_nonneg (1 - F x ^ 2), hε]
    calc
      _ = (F x ^ 2 * (1 - F x ^ 2)) / q x := by ring
      _ ≤ 1 := (div_le_one (hqpos x)).2 hnum
  have hcoef : 0 ≤ cutGradientConstant r * nearCount y r x :=
    mul_nonneg hK hnear_nonneg
  have hcoregrad := coreProduct_gradient_bound y hr x
  calc
    _ = (F x ^ 2 / q x) *
          (∑ i : Fin n, ∑ a : Fin 3,
            (fderiv ℝ F x (coordinateDirection i a)) ^ 2) := hsum
    _ ≤ (F x ^ 2 / q x) *
          ((1 - coreProduct y r x ^ 2) *
            (cutGradientConstant r * nearCount y r x)) :=
        mul_le_mul_of_nonneg_left hcoregrad (div_nonneg (sq_nonneg _) (hqpos x).le)
    _ ≤ cutGradientConstant r * nearCount y r x := by
      have hF : F x = coreProduct y r x := rfl
      rw [hF]
      calc
        _ = ((F x ^ 2 / q x) * (1 - F x ^ 2)) *
              (cutGradientConstant r * nearCount y r x) := by ring
        _ ≤ 1 * (cutGradientConstant r * nearCount y r x) :=
          mul_le_mul_of_nonneg_right hratio hcoef
        _ = cutGradientConstant r * nearCount y r x := by ring

theorem nearCount_nonneg {n : ℕ} (y : Position) (r : ℝ) (x : Configuration n) :
    0 ≤ nearCount y r x := by
  classical
  unfold nearCount
  apply Finset.sum_nonneg
  intro i hi
  change 0 ≤ (if x i ∈ Metric.closedBall y (2*r) then (1:ℝ) else 0)
  split_ifs <;> norm_num

theorem nearCount_le {n : ℕ} (y : Position) (r : ℝ) (x : Configuration n) :
    nearCount y r x ≤ n := by
  classical
  unfold nearCount
  calc
    (∑ i : Fin n, (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (x i)) ≤
        ∑ _i : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      change (if x i ∈ Metric.closedBall y (2*r) then (1:ℝ) else 0) ≤ 1
      split_ifs <;> norm_num
    _ = n := by simp

/-- The localization error of a multiplier whose squared gradient is controlled by the near count. -/
theorem localizationError_le_nearCount {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ)
    (y : Position) (r : ℝ) {K : ℝ}
    (hb : ∀ x, (∑ i : Fin n, ∑ a : Fin 3, (fderiv ℝ θ x (coordinateDirection i a)) ^ 2) ≤
      K * nearCount y r x) :
    localizationError ψ θ ≤ (1 / 2 : ℝ) * K * ∑ σ, ∫ x, nearCount y r x * ‖ψ σ x‖ ^ 2 := by
  classical
  have hnearMeas : Measurable (nearCount (n := n) y r) := by
    unfold nearCount
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_const.indicator measurableSet_closedBall).comp
      (continuous_apply i).measurable
  have hnearBound (x : Configuration n) : |nearCount y r x| ≤ n := by
    rw [abs_of_nonneg (nearCount_nonneg y r x)]
    exact nearCount_le y r x
  have hweighted (σ : Spins n) :
      Integrable (fun x : Configuration n => nearCount y r x * ‖ψ σ x‖ ^ 2) := by
    apply ((hψ σ).norm.integrable_sq).bdd_mul hnearMeas.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hnearBound x
  have hleft (σ : Spins n) : Integrable (fun x : Configuration n =>
      ∑ i : Fin n, ∑ a : Fin 3,
        (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2) := by
    exact integrable_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ (fun a ha =>
        integrable_localization_error hψ hθ σ i a))
  have hpoint (σ : Spins n) (x : Configuration n) :
      (∑ i : Fin n, ∑ a : Fin 3,
        (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2) ≤
        K * nearCount y r x * ‖ψ σ x‖ ^ 2 := by
    calc
      _ = (∑ i : Fin n, ∑ a : Fin 3,
            (fderiv ℝ θ x (coordinateDirection i a)) ^ 2) * ‖ψ σ x‖ ^ 2 := by
          simp only [Finset.sum_mul]
      _ ≤ K * nearCount y r x * ‖ψ σ x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hb x) (sq_nonneg _)
  have hspin (σ : Spins n) :
      (∑ i : Fin n, ∑ a : Fin 3,
        ∫ x : Configuration n,
          (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2) ≤
        K * ∫ x : Configuration n, nearCount y r x * ‖ψ σ x‖ ^ 2 := by
    have hsumInt :
        (∑ i : Fin n, ∑ a : Fin 3,
          ∫ x : Configuration n,
            (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2) =
        ∫ x : Configuration n, ∑ i : Fin n, ∑ a : Fin 3,
          (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2 := by
      calc
        _ = ∑ i : Fin n, ∫ x : Configuration n, ∑ a : Fin 3,
              (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          symm
          exact integral_finsetSum Finset.univ (fun a ha =>
            integrable_localization_error hψ hθ σ i a)
        _ = ∫ x : Configuration n, ∑ i : Fin n, ∑ a : Fin 3,
              (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2 := by
          symm
          exact integral_finsetSum Finset.univ (fun i hi =>
            integrable_finsetSum Finset.univ (fun a ha =>
              integrable_localization_error hψ hθ σ i a))
    have hright : Integrable (fun x : Configuration n =>
        K * nearCount y r x * ‖ψ σ x‖ ^ 2) := by
      simpa [mul_assoc] using (hweighted σ).const_mul K
    calc
      _ = ∫ x : Configuration n, ∑ i : Fin n, ∑ a : Fin 3,
            (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2 := hsumInt
      _ ≤ ∫ x : Configuration n, K * nearCount y r x * ‖ψ σ x‖ ^ 2 :=
        integral_mono (hleft σ) hright (fun z => hpoint σ z)
      _ = ∫ x : Configuration n, K *
            (nearCount y r x * ‖ψ σ x‖ ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = K * ∫ x : Configuration n, nearCount y r x * ‖ψ σ x‖ ^ 2 := by
        rw [integral_const_mul]
  unfold localizationError
  calc
    (1/2:ℝ) * (∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
        ∫ x : Configuration n,
          (fderiv ℝ θ x (coordinateDirection i a)) ^ 2 * ‖ψ σ x‖ ^ 2) ≤
      (1/2:ℝ) * (∑ σ : Spins n,
        K * ∫ x : Configuration n, nearCount y r x * ‖ψ σ x‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun σ hσ => hspin σ)
    _ = (1/2:ℝ) * K * ∑ σ : Spins n,
          ∫ x : Configuration n, nearCount y r x * ‖ψ σ x‖ ^ 2 := by
        rw [← Finset.mul_sum]
        ring

end

end AtomicIonization.IonizationGap
