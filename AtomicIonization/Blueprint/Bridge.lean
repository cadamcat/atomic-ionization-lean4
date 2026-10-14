import AtomicIonization.Challenge
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge

/-!
# Bridge to OpenAI's `CoulombRadii` library

The model of `AtomicIonization.Challenge` is a verbatim copy of OpenAI's `OAI.NeutralAtom` model,
so the two vocabularies agree definitionally.
-/

namespace AtomicIonization.Blueprint

open AtomicIonization

theorem formDomain_iff {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) :
    FormDomain ψ g ↔ OAI.NeutralAtom.FormDomain ψ g := Iff.rfl

theorem normSquared_eq {n : ℕ} (ψ : Wavefunction n) :
    normSquared ψ = OAI.NeutralAtom.normSquared ψ := rfl

theorem energy_eq {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) :
    energy Z ψ g = OAI.NeutralAtom.energy Z ψ g := rfl

theorem isNormalizedGroundState_iff (Z : ℕ) (ψ : Wavefunction Z) :
    IsNormalizedGroundState Z ψ ↔ OAI.NeutralAtom.IsNormalizedGroundState Z ψ := Iff.rfl

theorem density_eq {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) :
    density ψ x = OAI.NeutralAtom.density ψ x := rfl

theorem exteriorMass_eq {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) :
    exteriorMass ψ r = OAI.NeutralAtom.exteriorMass ψ r := rfl

end AtomicIonization.Blueprint
