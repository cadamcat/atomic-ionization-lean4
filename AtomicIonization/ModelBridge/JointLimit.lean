import AtomicIonization.ModelBridge.GroundEnergyLe
import OAI.Analysis.CoulombIonization.Main

namespace AtomicIonization.ModelBridge

open MeasureTheory
open AtomicIonization
open scoped ContDiff

private lemma local_lineDeriv_eq_openAI_fderiv {n : ℕ}
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Configuration n)
    (i : Fin n) (a : Fin 3) :
    Complex.ofReal (lineDeriv ℝ φ x (OAI.CoulombAtom.direction i a)) =
      (fderiv ℝ φ x (coordinateDirection i a) : ℂ) := by
  have h : lineDeriv ℝ φ x (coordinateDirection i a) =
      fderiv ℝ φ x (coordinateDirection i a) :=
    (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
  simpa [OAI.CoulombAtom.direction, coordinateDirection] using congrArg Complex.ofReal h

private lemma formDomain_iff_formAdmissible {n : ℕ} (ψ : Wavefunction n)
    (g : Gradient n) :
    (FormDomain ψ g ∧ normSquared ψ = 1) ↔
      OAI.CoulombAtom.FormAdmissible ⟨ψ, g⟩ := by
  constructor
  · rintro ⟨hd, hnorm⟩
    rcases hd with ⟨hanti, hweak, hψ, hg, hnuc, hpair⟩
    refine ⟨hψ, hg, ?_, ?_, ?_, ?_, ?_⟩
    · intro s i a φ hφ hcompact
      have hleft :
          (∫ x, ψ s x * Complex.ofReal (lineDeriv ℝ φ x
              (OAI.CoulombAtom.direction i a))) =
            ∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ s x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [local_lineDeriv_eq_openAI_fderiv φ hφ x i a]
        exact mul_comm _ _
      have hright :
          (∫ x, g s i a x * (φ x : ℂ)) = ∫ x, (φ x : ℂ) * g s i a x := by
        apply integral_congr_ae
        filter_upwards with x
        exact mul_comm _ _
      rw [hleft, hweak s i a φ hφ hcompact, hright]
    · intro π s
      exact hanti π s
    · exact hnorm
    · intro s i
      simpa [div_eq_mul_inv, mul_comm] using hnuc s i
    · intro s i j hij
      by_cases hlt : i < j
      · simpa [div_eq_mul_inv, mul_comm] using hpair s i j hlt
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
        simpa [div_eq_mul_inv, mul_comm, norm_sub_rev] using hpair s j i hji
  · intro hadm
    rcases hadm with ⟨hψ, hg, hweak, hanti, hnorm, hnuc, hpair⟩
    refine ⟨⟨?_, ?_, hψ, hg, ?_, ?_⟩, ?_⟩
    · intro π s
      exact hanti π s
    · intro s i a φ hφ hcompact
      have hleft :
          (∫ x, ψ s x * Complex.ofReal (lineDeriv ℝ φ x
              (OAI.CoulombAtom.direction i a))) =
            ∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ s x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [local_lineDeriv_eq_openAI_fderiv φ hφ x i a]
        exact mul_comm _ _
      have hright :
          (∫ x, g s i a x * (φ x : ℂ)) = ∫ x, (φ x : ℂ) * g s i a x := by
        apply integral_congr_ae
        filter_upwards with x
        exact mul_comm _ _
      rw [← hleft, ← hright]
      exact hweak s i a φ hφ hcompact
    · intro s i
      simpa [div_eq_mul_inv, mul_comm] using hnuc s i
    · intro s i j hij
      simpa [div_eq_mul_inv, mul_comm] using hpair s i j (Fin.ne_of_lt hij)
    · exact hnorm

private lemma coulombPotential_integral_eq {n : ℕ} (Z : ℕ) (ψ : Wavefunction n)
    (g : Gradient n) (hd : FormDomain ψ g) (s : Spins n) :
    (∫ x, coulombPotential Z x * ‖ψ s x‖ ^ 2) =
      -(Z : ℝ) * (∑ i : Fin n, ∫ x, ‖ψ s x‖ ^ 2 / ‖x i‖) +
        (∑ i : Fin n, ∑ j : Fin n,
          if i < j then ∫ x, ‖ψ s x‖ ^ 2 / ‖x i - x j‖ else 0) := by
  rcases hd with ⟨_, _, _, _, hnuc, hpair⟩
  let ρ : Configuration n → ℝ := fun x => ‖ψ s x‖ ^ 2
  have hnucInt (i : Fin n) : Integrable (fun x => ρ x / ‖x i‖) := by
    simpa [ρ, div_eq_mul_inv, mul_comm] using hnuc s i
  have hpairInt (i j : Fin n) :
      Integrable (fun x => if i < j then ρ x / ‖x i - x j‖ else 0) := by
    by_cases hij : i < j
    · simpa [ρ, hij, div_eq_mul_inv, mul_comm] using hpair s i j hij
    · simp [hij]
  have hnucSumInt : Integrable (fun x => ∑ i : Fin n, ρ x / ‖x i‖) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hnucInt i
  have hpairInnerInt (i : Fin n) :
      Integrable (fun x => ∑ j : Fin n, if i < j then ρ x / ‖x i - x j‖ else 0) := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hpairInt i j
  have hpairSumInt : Integrable (fun x =>
      ∑ i : Fin n, ∑ j : Fin n, if i < j then ρ x / ‖x i - x j‖ else 0) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hpairInnerInt i
  have hnucPoint (x : Configuration n) :
      (-(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹)) * ρ x =
        -(Z : ℝ) * (∑ i : Fin n, ρ x / ‖x i‖) := by
    calc
      (-(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹)) * ρ x =
          -(Z : ℝ) * ((∑ i : Fin n, ‖x i‖⁻¹) * ρ x) := by ring
      _ = -(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹ * ρ x) := by rw [Finset.sum_mul]
      _ = -(Z : ℝ) * (∑ i : Fin n, ρ x / ‖x i‖) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [div_eq_mul_inv, mul_comm]
  have hpairPoint (x : Configuration n) :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          ‖x i - x j‖⁻¹) * ρ x =
        ∑ i : Fin n, ∑ j : Fin n,
          if i < j then ρ x / ‖x i - x j‖ else 0 := by
    simp [Finset.mul_sum, Finset.sum_filter, div_eq_mul_inv, mul_comm]
  have hsplitPoint (x : Configuration n) :
      coulombPotential Z x * ρ x =
        (-(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹)) * ρ x +
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ‖x i - x j‖⁻¹) * ρ x := by
    unfold coulombPotential
    ring
  have hpairPotentialInt : Integrable (fun x =>
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        ‖x i - x j‖⁻¹) * ρ x) := by
    apply hpairSumInt.congr
    filter_upwards with x
    exact (hpairPoint x).symm
  calc
    ∫ x, coulombPotential Z x * ρ x =
        ∫ x, (-(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹)) * ρ x +
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ‖x i - x j‖⁻¹) * ρ x := by
      apply integral_congr_ae
      filter_upwards with x
      exact hsplitPoint x
    _ = (∫ x, (-(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹)) * ρ x) +
          ∫ x, (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ‖x i - x j‖⁻¹) * ρ x := by
      exact integral_add
        ((hnucSumInt.const_mul (-(Z : ℝ))).congr <| by
          filter_upwards with x
          exact (hnucPoint x).symm)
        hpairPotentialInt
    _ = -(Z : ℝ) * (∑ i : Fin n, ∫ x, ρ x / ‖x i‖) +
          ∫ x, (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ‖x i - x j‖⁻¹) * ρ x := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hnucPoint), integral_const_mul,
        integral_finsetSum Finset.univ (by intro i hi; exact hnucInt i)]
    _ = -(Z : ℝ) * (∑ i : Fin n, ∫ x, ρ x / ‖x i‖) +
          ∑ i : Fin n, ∑ j : Fin n,
            if i < j then ∫ x, ρ x / ‖x i - x j‖ else 0 := by
      congr 1
      calc
        ∫ x, (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ‖x i - x j‖⁻¹) * ρ x =
            ∫ x, ∑ i : Fin n, ∑ j : Fin n,
              if i < j then ρ x / ‖x i - x j‖ else 0 := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpairPoint x
        _ = ∑ i : Fin n, ∑ j : Fin n,
              if i < j then ∫ x, ρ x / ‖x i - x j‖ else 0 := by
          rw [integral_finsetSum Finset.univ (by intro i hi; exact hpairInnerInt i)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum Finset.univ (by intro j hj; exact hpairInt i j)]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hij : i < j <;> simp [hij]

private lemma energy_eq_formEnergy {n : ℕ} (Z : ℕ) (ψ : Wavefunction n)
    (g : Gradient n) (hd : FormDomain ψ g) :
    energy Z ψ g = OAI.CoulombAtom.formEnergy (Z : ℝ) ⟨ψ, g⟩ := by
  unfold energy OAI.CoulombAtom.formEnergy
  simp_rw [coulombPotential_integral_eq Z ψ g hd]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private lemma trialEnergySet_eq {n : ℕ} (Z : ℕ) :
    {e : ℝ | ∃ (ψ : Wavefunction n) (g : Gradient n),
      FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = e} =
    {e : ℝ | ∃ ψ : OAI.CoulombAtom.FormVector n,
      OAI.CoulombAtom.FormAdmissible ψ ∧
        OAI.CoulombAtom.formEnergy (Z : ℝ) ψ = e} := by
  ext e
  constructor
  · rintro ⟨ψ, g, hd, hnorm, he⟩
    refine ⟨⟨ψ, g⟩, (formDomain_iff_formAdmissible ψ g).mp ⟨hd, hnorm⟩, ?_⟩
    rw [← energy_eq_formEnergy Z ψ g hd]
    exact he
  · rintro ⟨v, hv, he⟩
    rcases v with ⟨ψ, g⟩
    obtain ⟨hd, hnorm⟩ := (formDomain_iff_formAdmissible ψ g).mpr hv
    refine ⟨ψ, g, hd, hnorm, ?_⟩
    rw [energy_eq_formEnergy Z ψ g hd]
    exact he

private lemma groundEnergy_eq_openAI_energy (Z n : ℕ) :
    groundEnergy Z n = OAI.CoulombAtom.energy (Z : ℝ) n := by
  by_cases hn0 : n = 0
  · simp [groundEnergy, OAI.CoulombAtom.energy, hn0]
  · simp [groundEnergy, OAI.CoulombAtom.energy, hn0, trialEnergySet_eq]

private lemma ionizationEnergy_eq_ionization (m Z : ℕ) :
    ionizationEnergy m Z = OAI.CoulombAtom.ionization m Z := by
  simp [ionizationEnergy, OAI.CoulombAtom.ionization, groundEnergy_eq_openAI_energy]

end AtomicIonization.ModelBridge

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

theorem joint_limit_proof :
    ∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧
      ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
        Filter.Tendsto m Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => ionizationEnergy (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
          Filter.atTop (nhds a) := by
  rcases OAI.CoulombAtom.generalized_ionization with ⟨a, ha, hTF, hJoint, _⟩
  refine ⟨a, ha, hTF, ?_⟩
  intro m Z hm hmtop hratio
  simpa only [AtomicIonization.ModelBridge.ionizationEnergy_eq_ionization] using
    hJoint m Z hm hmtop hratio


end AtomicIonization.Blueprint.Packages
