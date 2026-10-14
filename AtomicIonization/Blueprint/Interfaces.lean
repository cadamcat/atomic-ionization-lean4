import AtomicIonization.ModelBridge.GroundEnergyEqFormBottom
import AtomicIonization.ModelBridge.GroundEnergyLe
import AtomicIonization.ModelBridge.JointLimit
import AtomicIonization.UpperBound.IonizationUpper
import AtomicIonization.AtomicBinding.Binding
import AtomicIonization.AtomicBinding.GroundState
import AtomicIonization.HalfRadius.Large
import AtomicIonization.HalfRadius.Fixed
import AtomicIonization.IonizationGap.Package
import AtomicIonization.ExteriorTail.Tail

/-!
# Blueprint: package interfaces

Each `Packages.*` theorem is one step of the proof, stated in the vocabulary of
`AtomicIonization.Challenge`; `Main.lean` derives `Statement` from them. Each is proved as
`<name>_proof` in the module named in the README and restated here with its exact type.

References are to "Uniform excess charge for Coulomb molecules and the outer radius of neutral
atoms" (U).
-/

namespace AtomicIonization.Blueprint.Packages

open AtomicIonization

/-- Bridge: the sector energy equals OpenAI's form bottom of the atomic sector. -/
theorem groundEnergy_eq_formBottom (Z : ℕ) (hZ : 1 ≤ Z) (n : ℕ) :
    ((groundEnergy Z n : ℝ) : EReal) =
      OAI.Coulomb.sectorFormBottom (OAI.Coulomb.atom Z hZ) n :=
  groundEnergy_eq_formBottom_proof Z hZ n

/-- Bridge: the sector energy is a lower bound for the energy of every normalized vector of the
form domain. -/
theorem groundEnergy_le (Z n : ℕ) (hZ : 1 ≤ Z) (hn : 1 ≤ n) {ψ : Wavefunction n}
    {g : Gradient n} (hd : FormDomain ψ g) (hnorm : normSquared ψ = 1) :
    groundEnergy Z n ≤ energy Z ψ g :=
  groundEnergy_le_proof Z n hZ hn hd hnorm

/-- U, Lemma 2.5 (atomic binding): `E_Z(n) < E_Z(n-1)` for `1 ≤ n ≤ Z`. -/
theorem binding (Z n : ℕ) (hn : 1 ≤ n) (hnZ : n ≤ Z) :
    groundEnergy Z n < groundEnergy Z (n - 1) :=
  binding_proof Z n hn hnZ

/-- U, Lemma 2.5 (existence of ground states for `1 ≤ n ≤ Z`). -/
theorem groundState_exists (Z n : ℕ) (hn : 1 ≤ n) (hnZ : n ≤ Z) :
    ∃ (ψ : Wavefunction n) (g : Gradient n),
      FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = groundEnergy Z n :=
  groundState_exists_proof Z n hn hnZ

/-- U, Prop 12.3 with the finitely many small charges: `I₁(Z) ≤ C`. -/
theorem ionization_upper : ∃ C : ℝ, ∀ Z : ℕ, 1 ≤ Z → ionizationEnergy 1 Z ≤ C :=
  ionization_upper_proof

/-- U, Prop 13.1: a uniform positive ionization gap for large `Z`. -/
theorem ionization_gap :
    ∃ c : ℝ, 0 < c ∧ ∃ Z₂ : ℕ, ∀ Z : ℕ, Z₂ ≤ Z → 1 ≤ Z → c ≤ ionizationEnergy 1 Z :=
  ionization_gap_proof

/-- U, Prop 14.1: uniform exterior mass `∫_{|x|>R} ρ ≤ C / R` for large `Z` and `R ≥ R₀`. -/
theorem exterior_tail :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ ∃ Z₃ : ℕ, ∀ N : ℕ, Z₃ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
        ∀ R : ℝ, R₀ ≤ R → exteriorMass ψ R ≤ C / R :=
  exterior_tail_proof

/-- U, §12 (eq. tail-lower) and the completion of Thm 1.2: a uniform positive lower bound on the
half-electron radius for large `Z`. -/
theorem radius_lower_large :
    ∃ c : ℝ, 0 < c ∧ ∃ Z₀ : ℕ, ∀ N : ℕ, Z₀ ≤ N + 1 →
      ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ → c ≤ halfRadius ψ :=
  radius_lower_large_proof

/-- U, completion of Thm 1.2 for one fixed charge (compactness of the ground states and the
`L^{5/3}` density bound): two-sided bounds uniform over the ground states of that atom. -/
theorem radius_bounds_fixed (N : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ →
      c ≤ halfRadius ψ ∧ halfRadius ψ ≤ C :=
  radius_bounds_fixed_proof N

/-- G, Thm 1.1 (OpenAI's `OAI.CoulombAtom.generalized_ionization`), transported to this model. -/
theorem joint_limit :
    ∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧
      ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
        Filter.Tendsto m Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => ionizationEnergy (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
          Filter.atTop (nhds a) :=
  joint_limit_proof

end AtomicIonization.Blueprint.Packages
