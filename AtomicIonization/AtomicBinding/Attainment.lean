import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.Blueprint.Bridge
import AtomicIonization.Blueprint.Bridge
import OAI.Analysis.CoulombRadii.SpectralTheory.StrictBinding

namespace AtomicIonization.AtomicBinding

open OAI

theorem attained_of_binding (Z n : ℕ) (hn : 1 ≤ n) (hnZ : n ≤ Z)
    (hb : groundEnergy Z n < groundEnergy Z (n - 1)) :
    ∃ (ψ : Wavefunction n) (g : Gradient n),
      FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = groundEnergy Z n := by
  have hZ : 1 ≤ Z := hn.trans hnZ
  have hs : Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n <
      Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (n - 1) := by
    rw [← Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ n,
      ← Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ (n - 1)]
    exact EReal.coe_lt_coe_iff.mpr hb
  obtain ⟨u, ha, hm, he⟩ := Coulomb.atom_strict_binding_attained Z hZ
    (show 0 < n by omega) hs
  refine ⟨NeutralAtom.fromH1Wave u, NeutralAtom.fromH1Gradient u,
    NeutralAtom.fromH1_domain u ha, (NeutralAtom.fromH1_mass u).trans hm, ?_⟩
  change NeutralAtom.energy Z _ _ = _
  rw [NeutralAtom.fromH1_energy Z hZ]
  apply EReal.coe_eq_coe_iff.mp
  exact he.trans (Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ n).symm

theorem binding_one (Z : ℕ) (hZ : 1 ≤ Z) :
    groundEnergy Z 1 < groundEnergy Z 0 := by
  have hs := NeutralAtom.sectorEnergy_one_neg Z hZ
  rw [NeutralAtom.sectorEnergy_eq_formBottom Z hZ,
    ← Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ 1] at hs
  have hr : groundEnergy Z 1 < 0 := EReal.coe_lt_coe_iff.mp hs
  simpa [groundEnergy] using hr

end AtomicIonization.AtomicBinding
