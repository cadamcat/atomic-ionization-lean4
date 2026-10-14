import AtomicIonization.ExteriorTail.ShellWeight
import OAI.Analysis.CoulombRadii.FieldAnalysis.PotentialAddRsmul
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicWeightGeometry
import OAI.Analysis.CoulombRadii.RandomFields.CutJensen
import OAI.Analysis.CoulombRadii.Localization.RadialCut
import OAI.Analysis.CoulombRadii.Screening.CountMoments

/-!
# The state biased by its shell occupation

For a ground state `u` and `ε > 0`, multiplying by the smooth symmetric function
`F = √(ε + ∑ᵢ χ_r(xᵢ)²)` gives an antisymmetric state whose squared density is the squared
density of `u` weighted by `ε + ∑ᵢ χ_r(xᵢ)²`. The multiplier identity bounds its normalized energy
by the ground-state energy plus a gradient cost controlled by the expected shell population.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb MeasureTheory
open scoped ContDiff

noncomputable section

/-- The derivative constant of the shell weights. -/
def shellLip : ℝ := Classical.choose shell_derivative_bounds

theorem shellLip_nonneg : 0 ≤ shellLip := (Classical.choose_spec shell_derivative_bounds).1

theorem shellBump_deriv_le {r : ℝ} (hr : 0 < r) (b : Fin 3) (y : Space) :
    |fderiv ℝ (shellBump r) y (EuclideanSpace.single b 1)| ≤ shellLip / r :=
  (Classical.choose_spec shell_derivative_bounds).2.1 hr b y

theorem shellRoot_deriv_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {n : ℕ} (a : Fin n × Fin 3)
    (x : Configuration n) :
    |fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)| ≤ shellLip / r :=
  (Classical.choose_spec shell_derivative_bounds).2.2.1 hr hε x a

theorem shellRoot_grad_sq_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {n : ℕ}
    (x : Configuration n) :
    ∑ a : Fin n × Fin 3, (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 ≤
      3 * (shellLip / r) ^ 2 * localCount (imsShell 0 r) x :=
  (Classical.choose_spec shell_derivative_bounds).2.2.2 hr hε x

/-- The shell bump as a smooth bounded one-body coefficient. -/
def shellCoeff {r : ℝ} (hr : 0 < r) : SmoothBoundedCoefficient where
  value := shellBump r
  smooth := shellBump_contDiff r
  bound := 1
  derivBound := shellLip / r
  bound_nonneg := zero_le_one
  derivBound_nonneg := div_nonneg shellLip_nonneg hr.le
  value_le y := by rw [abs_of_nonneg (shellBump_nonneg r y)]; exact shellBump_le_one r y
  deriv_le b y := shellBump_deriv_le hr b y

/-- The shell occupation `∑ᵢ χ_r(xᵢ)²`. -/
def shellCount (r : ℝ) {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i, (shellBump r (position x i)) ^ 2

theorem shellCount_nonneg (r : ℝ) {n : ℕ} (x : Configuration n) : 0 ≤ shellCount r x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem shellCount_le (r : ℝ) {n : ℕ} (x : Configuration n) : shellCount r x ≤ n := by
  unfold shellCount
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
      have h0 := shellBump_nonneg r (position x i)
      have h1 := shellBump_le_one r (position x i)
      nlinarith
    _ = n := by simp

theorem measurable_shellBump (r : ℝ) : Measurable (shellBump r) :=
  (shellBump_contDiff r).continuous.measurable

theorem measurable_shellCount (r : ℝ) {n : ℕ} : Measurable (shellCount r (n := n)) := by
  unfold shellCount
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_shellBump r).comp (continuous_position i).measurable).pow_const 2

/-- `u` multiplied by `√(ε + ∑ᵢ χ_r(xᵢ)²)`. -/
def biasMul {n : ℕ} (u : H1Vector n) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) : H1Vector n :=
  u.smoothMul (shellRoot r ε) (shellRoot_contDiff hε n) (Real.sqrt (ε + n)) (shellLip / r)
    (abs_shellRoot_le hε.le) (shellRoot_deriv_le hr hε)

theorem potentialForm_biasMul {n : ℕ} (u : H1Vector n) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (V : Configuration n → ℝ) :
    potentialForm V (biasMul u hr hε) = potentialForm (fun x => V x * (ε + shellCount r x)) u := by
  unfold potentialForm
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [] with x
  change V x * ‖(shellRoot r ε x : ℂ) * u.value s x‖ ^ 2 = _
  rw [norm_real_mul_sq, shellRoot_sq hε.le]
  unfold shellCount
  ring

theorem mass_eq_potentialForm_one {n : ℕ} (u : H1Vector n) :
    mass u = potentialForm (fun _ => (1 : ℝ)) u := by
  simp [mass, potentialForm]

theorem mass_biasMul {n : ℕ} (u : H1Vector n) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    mass (biasMul u hr hε) = ε * mass u + potentialForm (shellCount r) u := by
  rw [mass_eq_potentialForm_one, potentialForm_biasMul, mass_eq_potentialForm_one]
  have h1 : ∀ s, Integrable (fun x => (fun _ => ε) x * ‖u.value s x‖ ^ 2) := fun s =>
    boundedObservable_integrable u (fun _ => ε) measurable_const (B := |ε|) (fun _ => le_rfl) s
  have h2 : ∀ s, Integrable (fun x => shellCount r x * ‖u.value s x‖ ^ 2) := fun s =>
    boundedObservable_integrable u _ (measurable_shellCount r) (B := n)
      (fun x => by rw [abs_of_nonneg (shellCount_nonneg r x)]; exact shellCount_le r x) s
  have he : (fun x : Configuration n => 1 * (ε + shellCount r x)) =
      fun x => (fun _ => ε) x + shellCount r x := by funext x; ring
  rw [he, potentialForm_add u _ _ h1 h2]
  congr 1
  simp only [potentialForm, integral_const_mul, ← Finset.mul_sum, one_mul]

theorem groundState_of_min (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} (hn : n ≠ 0) (u : H1Vector n)
    (ha : Antisymmetric u) (hm : mass u = 1)
    (hmin : (form (atom Z hZ) u : EReal) = sectorFormBottom (atom Z hZ) n) :
    GroundState (atom Z hZ) u := by
  refine ⟨ha, hm, ?_⟩
  unfold energy
  simp only [hn, ↓reduceIte]
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨u, ha, hm, rfl⟩, ?_⟩
  rintro e ⟨v, hv, hvm, rfl⟩
  have H : sectorFormBottom (atom Z hZ) n ≤ (form (atom Z hZ) v : EReal) :=
    sInf_le ⟨v, hv, hvm, rfl⟩
  rw [← hmin] at H
  exact EReal.coe_le_coe_iff.mp H

theorem form_biasMul {Z : ℕ} {hZ : 1 ≤ Z} {n : ℕ} (hn : n ≠ 0) {u : H1Vector n}
    (hu : GroundState (atom Z hZ) u) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    form (atom Z hZ) (biasMul u hr hε) =
      form (atom Z hZ) u * mass (biasMul u hr hε) +
        (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
          (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 *
            ‖u.value s x‖ ^ 2 := by
  have H := hu.smooth_multiplier_identity hn (shellRoot r ε) (shellRoot_contDiff hε n)
    (Real.sqrt (ε + n)) (shellLip / r) (abs_shellRoot_le hε.le) (shellRoot_deriv_le hr hε)
    (shellRoot_permute r ε)
  rw [← hu.2.2] at H
  exact H

theorem biasMul_gradient_le {n : ℕ} (u : H1Vector n) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 *
          ‖u.value s x‖ ^ 2 ≤
      (3 / 2) * (shellLip / r) ^ 2 * expectedPopulation u (imsShell 0 r) := by
  have hcont : ∀ a : Fin n × Fin 3,
      Continuous (fun x => fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) :=
    fun a => ((shellRoot_contDiff hε n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : ∀ (a : Fin n × Fin 3) s, Integrable (fun x =>
      (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 *
        ‖u.value s x‖ ^ 2) := fun a s =>
    boundedObservable_integrable u _ ((hcont a).measurable.pow_const 2)
      (B := (shellLip / r) ^ 2) (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h := shellRoot_deriv_le hr hε a x
        have h2 := (sq_le_sq₀ (abs_nonneg _) (div_nonneg shellLip_nonneg hr.le)).mpr h
        rwa [sq_abs] at h2) s
  have hsum : (∑ s, ∑ a, ∫ x,
      (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2 *
        ‖u.value s x‖ ^ 2) = potentialForm (fun x => ∑ a : Fin n × Fin 3,
          (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2) u := by
    unfold potentialForm
    apply Finset.sum_congr rfl
    intro s _
    rw [← integral_finsetSum _ (fun a _ => hi a s)]
    congr 1
    funext x
    rw [Finset.sum_mul]
  have hA : MeasurableSet (imsShell (0 : Space) r) := measurableSet_imsShell 0 r
  have hloc : Measurable (localCount (n := n) (imsShell 0 r)) := localCount_measurable hA
  have hmono := potentialForm_mono_ae u
    (fun x => ∑ a : Fin n × Fin 3,
      (fderiv ℝ (shellRoot r ε (n := n)) x (EuclideanSpace.single a 1)) ^ 2)
    (fun x => 3 * (shellLip / r) ^ 2 * localCount (imsShell 0 r) x)
    (fun s => by
      have := integrable_finsetSum (Finset.univ) (fun a _ => hi a s)
      simpa only [Finset.sum_mul] using this)
    (fun s => boundedObservable_integrable u _ (measurable_const.mul hloc)
      (B := 3 * (shellLip / r) ^ 2 * n) (fun x => by
        change |3 * (shellLip / r) ^ 2 * localCount (imsShell 0 r) x| ≤ _
        rw [abs_of_nonneg (mul_nonneg (by positivity) (localCount_nonneg _ _))]
        exact mul_le_mul_of_nonneg_left (localCount_le _ _) (by positivity)) s)
    (Filter.Eventually.of_forall fun x => shellRoot_grad_sq_le hr hε x)
  rw [hsum]
  have hpop : potentialForm (fun x => 3 * (shellLip / r) ^ 2 * localCount (imsShell 0 r) x) u =
      3 * (shellLip / r) ^ 2 * expectedPopulation u (imsShell 0 r) := by
    rw [expectedPopulation_eq u hA]
    simp only [potentialForm, mul_assoc, integral_const_mul, ← Finset.mul_sum]
  rw [hpop] at hmono
  linarith

end

end AtomicIonization.ExteriorTail
