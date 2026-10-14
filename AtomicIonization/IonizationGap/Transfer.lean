import OAI.Analysis.CoulombRadii.Propagation.UniformScreening
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge

/-!
# Uniform screening estimates in the configuration-space vocabulary

Two consequences of the uniform local screening estimates for atomic states with an arbitrary
energy offset `δ`, transported to wavefunctions on `Fin n → ℝ³`:
* the positive part of the expected unscreened field at a center `y`, keeping only the electrons
  at distance at least `40 a` with `a = |y|/100000`, is at most a universal multiple of
  `screenMass δ a / a`;
* the expected number of electrons in the annulus `u/2 < |x| < 3u` is at most a universal multiple
  of `screenMass δ u`.
-/

namespace AtomicIonization.IonizationGap

open OAI OAI.NeutralAtom MeasureTheory

noncomputable section

/-- Expected Coulomb potential at `y` of the electrons at distance at least `ρ` from `y`. -/
def farPotential {n : ℕ} (ψ : Wavefunction n) (y : Position) (ρ : ℝ) : ℝ :=
  ∑ σ, ∑ i : Fin n, ∫ x : Configuration n,
    if x i ∈ {z : Position | ρ ≤ ‖z - y‖} then ‖x i - y‖⁻¹ * ‖ψ σ x‖ ^ 2 else 0

/-- Expected number of electrons in a set `A`. -/
def populationOf {n : ℕ} (ψ : Wavefunction n) (A : Set Position) : ℝ :=
  ∑ σ, ∑ i : Fin n, ∫ x : Configuration n, A.indicator (fun _ => (1 : ℝ)) (x i) * ‖ψ σ x‖ ^ 2

theorem restrictedCorePotential_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (y : Position) (ρ : ℝ) :
    Coulomb.restrictedCorePotential (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      {z | ρ ≤ ‖z - y‖} y = farPotential ψ y ρ := by
  unfold Coulomb.restrictedCorePotential farPotential
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  rw [← (flattenConfiguration_measurePreserving n).integral_comp']
  rfl

theorem expectedPopulation_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (A : Set Position) :
    Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) A = populationOf ψ A := by
  unfold Coulomb.expectedPopulation populationOf
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  rw [← (flattenConfiguration_measurePreserving n).integral_comp']
  rfl

/-- The expected unscreened field at a far center, at an arbitrary energy offset. -/
theorem far_field_bound : ∃ Cf P : ℝ, 0 ≤ Cf ∧ 1 ≤ P ∧
    ∀ (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} {ψ : Wavefunction n} {g : Gradient n},
      FormDomain ψ g → normSquared ψ = 1 →
      ∀ {E δ : ℝ}, (E : EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
        energy Z ψ g ≤ E + δ → 0 ≤ δ → ∀ {y : Position}, y ≠ 0 →
          (Z : ℝ) * ‖y‖⁻¹ - farPotential ψ y (40 * (‖y‖ / 100000)) ≤
            Cf * (Real.sqrt P * Coulomb.screenMass δ (‖y‖ / 100000) / (‖y‖ / 100000)) := by
  refine ⟨2 * Coulomb.atomicBudgetRecursionC ^ 2, Coulomb.atomicCountConstant, by positivity,
    by linarith [Coulomb.atomicCountConstant_ge_two], ?_⟩
  intro Z hZ n ψ g hd hn E δ hE he hδ y hy
  have H := Coulomb.atomic_expected_raw_field_bound (Coulomb.atom Z hZ) (fun _ => rfl)
    (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) (asH1_antisymmetric hd)
    ((asH1_mass _ _ _).trans hn) hE (by rw [asH1_energy Z hZ]; exact he) hδ hy
  rw [restrictedCorePotential_asH1 hd] at H
  have hatt : Coulomb.attraction (Coulomb.atom Z hZ) y = (Z : ℝ) * ‖y‖⁻¹ := by
    simp [Coulomb.attraction, Coulomb.atom, Coulomb.coulombKernel]
  rw [hatt] at H
  exact (le_max_left _ _).trans H

/-- The expected number of electrons in the annulus `u/2 < |x| < 3u`, at an arbitrary offset. -/
theorem annular_population_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} {ψ : Wavefunction n} {g : Gradient n},
      FormDomain ψ g → normSquared ψ = 1 →
      ∀ {E δ : ℝ}, (E : EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
        energy Z ψ g ≤ E + δ → 0 ≤ δ → ∀ {u : ℝ}, 0 < u →
          populationOf ψ {z : Position | 1 / 2 * u < ‖z‖ ∧ ‖z‖ < 3 * u} ≤
            C * Coulomb.screenMass δ u := by
  obtain ⟨C₀, hC₀, H⟩ := Coulomb.atomic_annular_second_moment (α := 1 / 2) (β := 3)
    (by norm_num) (by norm_num)
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, ?_⟩
  intro Z hZ n ψ g hd hn E δ hE he hδ u hu
  let v := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have hm : Coulomb.mass v = 1 := (asH1_mass _ _ _).trans hn
  have hA : MeasurableSet {z : Position | 1 / 2 * u < ‖z‖ ∧ ‖z‖ < 3 * u} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have h2 := H (Coulomb.atom Z hZ) (fun _ => rfl) v (asH1_antisymmetric hd) hm hE
    (by rw [asH1_energy Z hZ]; exact he) hδ hu
  have h1 := Coulomb.expectedPopulation_sq_le v hA hm
  rw [expectedPopulation_asH1 hd] at h1
  have h3 := Real.abs_le_sqrt (h1.trans h2)
  rw [Real.sqrt_mul hC₀, Real.sqrt_sq (Coulomb.screenMass_pos δ u).le] at h3
  exact (le_abs_self _).trans h3

end

end AtomicIonization.IonizationGap
