import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.Blueprint.Finite
import AtomicIonization.Blueprint.Bridge
import AtomicIonization.Blueprint.Bridge
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralBaseline

namespace AtomicIonization.UpperBound

open AtomicIonization

theorem real_eq_of_ereal_coe_eq {x y : ℝ} (h : (x : EReal) = (y : EReal)) : x = y := by
  apply le_antisymm
  · exact EReal.coe_le_coe_iff.mp (le_of_eq h)
  · exact EReal.coe_le_coe_iff.mp (le_of_eq h.symm)

end AtomicIonization.UpperBound

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

theorem ionization_upper_proof :
    ∃ C : ℝ, ∀ Z : ℕ, 1 ≤ Z → ionizationEnergy 1 Z ≤ C := by
  obtain ⟨D, _, Zmin, hOffset⟩ := OAI.NeutralAtom.physical_uniform_predecessor_offset
  obtain ⟨Csmall, hsmall⟩ := AtomicIonization.Blueprint.finite_upper
    (fun Z C => ionizationEnergy 1 Z ≤ C)
    (fun _ C C' hCC' h => h.trans hCC') Zmin
    (fun Z _ => ⟨ionizationEnergy 1 Z, le_rfl⟩)
  refine ⟨max D Csmall, fun Z hZ => ?_⟩
  by_cases hLarge : Zmin ≤ Z
  · have hPreOffset := hOffset Z hLarge hZ
    have hPrevReal := OAI.Coulomb.atom_sectorFormBottom_real Z hZ (Z - 1)
    have hNeutralReal := OAI.Coulomb.atom_sectorFormBottom_real Z hZ Z
    obtain ⟨_, _, _, u, ha, hm, _⟩ := OAI.Coulomb.atom_global_sector_minimum Z hZ
    have hUnrestrictedReal := OAI.Coulomb.atom_unrestricted_bottom_real Z hZ u ha hm
    have hUnrestrictedLeNeutral :
        OAI.Coulomb.unrestrictedFormBottom (OAI.Coulomb.atom Z hZ) ≤
          OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) Z := by
      have h := OAI.NeutralAtom.unrestrictedEnergy_le_sector Z Z
      rw [OAI.NeutralAtom.unrestrictedEnergy_eq_formBottom Z hZ,
        OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ Z] at h
      exact h
    have hUnrestrictedRealLeNeutralReal :
        (OAI.Coulomb.unrestrictedFormBottom (OAI.Coulomb.atom Z hZ)).toReal ≤
          (OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) Z).toReal := by
      apply EReal.coe_le_coe_iff.mp
      rw [hUnrestrictedReal, hNeutralReal]
      exact hUnrestrictedLeNeutral
    have hGroundPrev : groundEnergy Z (Z - 1) =
        (OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) (Z - 1)).toReal := by
      apply AtomicIonization.UpperBound.real_eq_of_ereal_coe_eq
      exact (AtomicIonization.Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ (Z - 1)).trans
        hPrevReal.symm
    have hGroundNeutral : groundEnergy Z Z =
        (OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) Z).toReal := by
      apply AtomicIonization.UpperBound.real_eq_of_ereal_coe_eq
      exact (AtomicIonization.Blueprint.Packages.groundEnergy_eq_formBottom_proof Z hZ Z).trans
        hNeutralReal.symm
    have hLargeEnergy : ionizationEnergy 1 Z ≤ D := by
      change groundEnergy Z (Z - 1) - groundEnergy Z Z ≤ D
      rw [hGroundPrev, hGroundNeutral]
      linarith
    exact hLargeEnergy.trans (le_max_left _ _)
  · have hSmall : Z < Zmin := Nat.lt_of_not_ge hLarge
    exact (hsmall Z hSmall).trans (le_max_right _ _)

end AtomicIonization.Blueprint.Packages


