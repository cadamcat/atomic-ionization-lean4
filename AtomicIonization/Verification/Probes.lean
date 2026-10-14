import AtomicIonization.Challenge

/-!
# Probes of the statement's definitions

Small kernel-checked facts about the definitions behind `AtomicIonization.Statement`.
-/

namespace AtomicIonization.Verification

open AtomicIonization

/-- The vacuum sector has energy `0`. -/
example (Z : ℕ) : groundEnergy Z 0 = 0 := by simp [groundEnergy]

/-- For hydrogen, `I₁(1) = E_1(0) - E_1(1) = -E_1(1)`. -/
example : ionizationEnergy 1 1 = -groundEnergy 1 1 := by
  simp [ionizationEnergy, groundEnergy]

/-- `I_m(Z)` removes `m` electrons from the neutral atom: `E_Z(Z - m) - E_Z(Z)`. -/
example : ionizationEnergy 2 5 = groundEnergy 5 3 - groundEnergy 5 5 := rfl

/-- The half-electron radius is nonnegative for every wavefunction. -/
example {N : ℕ} (ψ : Wavefunction (N + 1)) : 0 ≤ halfRadius ψ :=
  Real.sInf_nonneg fun _ hr => hr.1

/-- Two electrons: the potential is `-Z/|x₀| - Z/|x₁| + 1/|x₀ - x₁|`. -/
example (Z : ℕ) (x : Configuration 2) :
    coulombPotential Z x = -(Z : ℝ) * (‖x 0‖⁻¹ + ‖x 1‖⁻¹) + ‖x 0 - x 1‖⁻¹ := by
  simp only [coulombPotential, Finset.sum_filter, Fin.sum_univ_two]
  norm_num

end AtomicIonization.Verification
