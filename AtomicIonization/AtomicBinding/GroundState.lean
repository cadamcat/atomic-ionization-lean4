import AtomicIonization.AtomicBinding.Binding

namespace AtomicIonization.Blueprint.Packages

theorem groundState_exists_proof (Z n : ℕ) (hn : 1 ≤ n) (hnZ : n ≤ Z) :
    ∃ (ψ : Wavefunction n) (g : Gradient n),
      FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = groundEnergy Z n :=
  AtomicBinding.attained_of_binding Z n hn hnZ (binding_proof Z n hn hnZ)



end AtomicIonization.Blueprint.Packages
