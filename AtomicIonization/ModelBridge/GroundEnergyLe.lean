import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.Blueprint.Bridge

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

theorem groundEnergy_le_proof (Z n : ℕ) (hZ : 1 ≤ Z) (hn : 1 ≤ n)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hnorm : normSquared ψ = 1) :
    groundEnergy Z n ≤ energy Z ψ g := by
  apply EReal.coe_le_coe_iff.mp
  rw [groundEnergy_eq_formBottom_proof Z hZ n,
    ← OAI.NeutralAtom.sectorEnergy_eq_formBottom Z hZ n]
  exact OAI.NeutralAtom.sectorEnergy_le_trial
    (Z := Z) (ψ := ψ) (g := g)
    (show OAI.NeutralAtom.FormDomain ψ g from hd)
    (show OAI.NeutralAtom.normSquared ψ = 1 from hnorm)


end AtomicIonization.Blueprint.Packages
