import AtomicIonization.IonizationGap.Package
import AtomicIonization.Blueprint.Bridge
import AtomicIonization.ExteriorTail.ShellBound
import AtomicIonization.ExteriorTail.ShellSum
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralBaseline
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge

/-!
# Uniform exterior mass of neutral atoms

A uniform positive ionization gap and the uniformly bounded energy offset of neutral ground
states give, through the shell estimate, `∫_{|x|>R} ρ ≤ C / R` for `R ≥ R₀` and all large `Z`.
-/

namespace AtomicIonization.ExteriorTail

open OAI Coulomb MeasureTheory

theorem groundEnergy_eq_of_isNormalizedGroundState {N : ℕ} {ψ : Wavefunction (N + 1)}
    {g : Gradient (N + 1)} (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)),
      FormDomain χ h → normSquared χ = 1 → energy (N + 1) ψ g ≤ energy (N + 1) χ h) :
    groundEnergy (N + 1) (N + 1) = energy (N + 1) ψ g := by
  unfold groundEnergy
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  apply IsLeast.csInf_eq
  refine ⟨⟨ψ, g, hd, hn, rfl⟩, ?_⟩
  rintro e ⟨χ, h, hχ, hχn, rfl⟩
  exact hmin χ h hχ hχn

theorem groundEnergy_le_formBottom (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} (hn : n ≠ 0) :
    ((groundEnergy Z n : ℝ) : EReal) ≤ sectorFormBottom (atom Z hZ) n := by
  apply le_sInf
  rintro e ⟨v, hv, hvm, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  unfold groundEnergy
  simp only [hn, ↓reduceIte]
  apply csInf_le
  · refine ⟨(sectorFormBottom (atom Z hZ) n).toReal, ?_⟩
    rintro e ⟨χ, h, hχ₀, hχn, rfl⟩
    have hχ : NeutralAtom.FormDomain χ h := hχ₀
    have H : sectorFormBottom (atom Z hZ) n ≤
        (form (atom Z hZ) (NeutralAtom.asH1 χ h hχ.2.1 hχ.2.2.1 hχ.2.2.2.1) : EReal) :=
      sInf_le ⟨_, NeutralAtom.asH1_antisymmetric hχ, (NeutralAtom.asH1_mass ..).trans hχn, rfl⟩
    rw [NeutralAtom.asH1_energy Z hZ, ← atom_sectorFormBottom_real Z hZ n] at H
    exact EReal.coe_le_coe_iff.mp H
  · exact ⟨NeutralAtom.fromH1Wave v, NeutralAtom.fromH1Gradient v, NeutralAtom.fromH1_domain v hv,
      (NeutralAtom.fromH1_mass v).trans hvm, NeutralAtom.fromH1_energy Z hZ v⟩

theorem expectedPopulation_shell_le_shellCount {n : ℕ} (u : H1Vector n) {r : ℝ} (hr : 0 < r) :
    expectedPopulation u {y : Space | 9 / 8 * r ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * r} ≤
      potentialForm (shellCount r) u := by
  have hA : MeasurableSet {y : Space | 9 / 8 * r ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * r} :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  rw [expectedPopulation_eq u hA]
  apply potentialForm_mono_ae u
  · exact fun s => boundedObservable_integrable u _ (localCount_measurable hA) (B := n)
      (fun x => by rw [abs_of_nonneg (localCount_nonneg _ _)]; exact localCount_le _ _) s
  · exact fun s => boundedObservable_integrable u _ (measurable_shellCount r) (B := n)
      (fun x => by rw [abs_of_nonneg (shellCount_nonneg r x)]; exact shellCount_le r x) s
  · refine Filter.Eventually.of_forall fun x => ?_
    unfold localCount shellCount
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : position x i ∈ {y : Space | 9 / 8 * r ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * r}
    · rw [Set.indicator_of_mem hi, shellBump_eq_one hr hi.1 hi.2]; norm_num
    · rw [Set.indicator_of_notMem hi]; exact sq_nonneg _

end AtomicIonization.ExteriorTail

open AtomicIonization OAI Coulomb in
/-- Uniform exterior mass of neutral ground states, given a uniform positive ionization gap. -/
theorem AtomicIonization.ExteriorTail.exterior_tail_of_gap
    (hgap₀ : ∃ c : ℝ, 0 < c ∧ ∃ Z₂ : ℕ, ∀ Z : ℕ, Z₂ ≤ Z → 1 ≤ Z → c ≤ ionizationEnergy 1 Z) :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ ∃ Z₃ : ℕ, ∀ N : ℕ, Z₃ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
        ∀ R : ℝ, R₀ ≤ R → exteriorMass ψ R ≤ C / R := by
  obtain ⟨c, hc, Z₂, hgap⟩ := hgap₀
  obtain ⟨D, hD, Zmin, Hoff⟩ := NeutralAtom.physical_neutral_energy_offset
  obtain ⟨K, r₁, hK, hr₁, Hshell⟩ := ExteriorTail.shell_mass_bound hD hc
  refine ⟨3 * K, 9 / 8 * r₁, by positivity, max (max Z₂ Zmin) 2, ?_⟩
  intro N hN ψ hψ R hR
  obtain ⟨g, hd₀, hn, hmin⟩ := hψ
  have hd : NeutralAtom.FormDomain ψ g := hd₀
  have hZ : 1 ≤ N + 1 := by omega
  have hN1 : N ≠ 0 := by omega
  set u := NeutralAtom.asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have ha : Antisymmetric u := NeutralAtom.asH1_antisymmetric hd
  have hm : mass u = 1 := (NeutralAtom.asH1_mass ..).trans hn
  have hform : form (atom (N + 1) hZ) u = energy (N + 1) ψ g := NeutralAtom.asH1_energy (N + 1) hZ ..
  have hminE : (form (atom (N + 1) hZ) u : EReal) = sectorFormBottom (atom (N + 1) hZ) (N + 1) := by
    rw [hform, ← NeutralAtom.sectorEnergy_eq_formBottom (N + 1) hZ]
    apply le_antisymm
    · apply le_sInf
      rintro e ⟨χ, h, hχ, hχn, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmin χ h hχ hχn)
    · exact NeutralAtom.sectorEnergy_le_trial hd hn
  set E := (unrestrictedFormBottom (atom (N + 1) hZ)).toReal
  have hE : (E : EReal) ≤ unrestrictedFormBottom (atom (N + 1) hZ) :=
    (atom_unrestricted_bottom_real (N + 1) hZ u ha hm).le
  have hoff : form (atom (N + 1) hZ) u ≤ E + D := by
    rw [hform]
    exact Hoff (N + 1) (by omega) hZ hd hn hmin
  have hP : ((groundEnergy (N + 1) N : ℝ) : EReal) ≤ sectorFormBottom (atom (N + 1) hZ) (N + 1 - 1) := by
    simpa using ExteriorTail.groundEnergy_le_formBottom (N + 1) hZ hN1
  have hgap' : c ≤ groundEnergy (N + 1) N - form (atom (N + 1) hZ) u := by
    have h := hgap (N + 1) (by omega) hZ
    unfold ionizationEnergy at h
    rw [ExteriorTail.groundEnergy_eq_of_isNormalizedGroundState hd₀ hn hmin] at h
    simpa [hform] using h
  have hshell : ∀ r : ℝ, r₁ ≤ r →
      expectedPopulation u {y : Space | 9 / 8 * r ≤ ‖y‖ ∧ ‖y‖ ≤ 15 / 8 * r} ≤ K / r := by
    intro r hr
    have hr0 : 0 < r := by linarith
    exact (ExteriorTail.expectedPopulation_shell_le_shellCount u hr0).trans
      (Hshell (N + 1) hZ hZ u ha hm hminE hE hoff hP hgap' r hr)
  have H := ExteriorTail.expectedPopulation_exterior_le u (by linarith) hK hshell R hR
  rw [← ExteriorTail.exteriorMass_eq_expectedPopulation hd R] at H
  exact H

open AtomicIonization in
theorem AtomicIonization.Blueprint.Packages.exterior_tail_proof :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ ∃ Z₃ : ℕ, ∀ N : ℕ, Z₃ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
        ∀ R : ℝ, R₀ ≤ R → exteriorMass ψ R ≤ C / R :=
  AtomicIonization.ExteriorTail.exterior_tail_of_gap AtomicIonization.Blueprint.Packages.ionization_gap_proof

