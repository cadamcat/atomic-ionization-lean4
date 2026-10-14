import AtomicIonization.IonizationGap.Gap
import AtomicIonization.Blueprint.Bridge
import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.AtomicBinding.GroundState
import AtomicIonization.AtomicBinding.GroundState

/-!
# A uniform positive first ionization energy for large nuclear charge

The ground state of the singly ionized atom exists, its energy is the bottom of its sector, and
the neutral sector energy is a lower bound for every normalized neutral trial state. The
insertion argument then gives `E_Z(Z) ≤ E_Z(Z - 1) - c` for all large `Z`.
-/

namespace AtomicIonization.IonizationGap

open AtomicIonization

/-- The sector energy is a lower bound for the energy of every normalized trial state. -/
theorem groundEnergy_le_trial (Z : ℕ) (hZ : 1 ≤ Z) {n : ℕ} {ψ : Wavefunction n}
    {g : Gradient n} (hd : FormDomain ψ g) (hn : normSquared ψ = 1) :
    groundEnergy Z n ≤ energy Z ψ g := by
  have h1 := Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ n
  rw [← OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ n] at h1
  have h2 := OAI.NeutralAtom.sectorEnergy_le_trial (Z := Z) hd hn
  rw [← h1] at h2
  exact EReal.coe_le_coe_iff.mp h2

end AtomicIonization.IonizationGap

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

theorem ionization_gap_proof :
    ∃ c : ℝ, 0 < c ∧ ∃ Z₂ : ℕ, ∀ Z : ℕ, Z₂ ≤ Z → 1 ≤ Z → c ≤ ionizationEnergy 1 Z := by
  obtain ⟨c, hc, Z₂, H⟩ := AtomicIonization.IonizationGap.gap_core
  refine ⟨c, hc, max Z₂ 2, ?_⟩
  intro Z hZ hZ1
  obtain ⟨N, rfl⟩ : ∃ N, Z = N + 1 := ⟨Z - 1, by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hZ₂ : Z₂ ≤ N + 1 := le_trans (le_max_left _ _) hZ
  have hZ' : 1 ≤ N + 1 := Nat.le_add_left 1 N
  obtain ⟨Φ, g, hd, hn, he⟩ := groundState_exists_proof (N + 1) N hN1 (Nat.le_succ N)
  have hmin : ∀ (χ : Wavefunction N) (h : Gradient N), FormDomain χ h → normSquared χ = 1 →
      energy (N + 1) Φ g ≤ energy (N + 1) χ h := by
    intro χ h hχ hnχ
    rw [he]
    exact AtomicIonization.IonizationGap.groundEnergy_le_trial (N + 1) hZ' hχ hnχ
  have hsec : ((energy (N + 1) Φ g : ℝ) : EReal) =
      OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom (N + 1) (Nat.le_add_left 1 N)) N := by
    rw [he]
    exact groundEnergy_eq_formBottom_proof (N + 1) hZ' N
  have hE' : ∀ (χ : Wavefunction (N + 1)) (h : Gradient (N + 1)), FormDomain χ h →
      normSquared χ = 1 → groundEnergy (N + 1) (N + 1) ≤ energy (N + 1) χ h :=
    fun χ h hχ hnχ => AtomicIonization.IonizationGap.groundEnergy_le_trial (N + 1) hZ' hχ hnχ
  have hgap : groundEnergy (N + 1) (N + 1) ≤ energy (N + 1) Φ g - c :=
    H N hZ₂ hd hn hmin hsec hE'
  rw [he] at hgap
  unfold ionizationEnergy
  rw [Nat.add_sub_cancel]
  linarith


end AtomicIonization.Blueprint.Packages
