import Mathlib

/-!
# Ionization bounds and generalized ionization asymptotics for Coulomb atoms

The full nonrelativistic Coulomb atom: one nucleus of integer charge `Z` fixed at the origin,
`n` electrons with two spin states, kinetic term `-Δ/2`, and wavefunctions antisymmetric in the
joint space–spin variables. The Hamiltonian is taken through its quadratic form on the
antisymmetric `H¹` form domain.

The model (form domain, energy functional, normalized ground states, spin-summed density and
exterior mass) is copied verbatim from OpenAI's Comparator challenge
`ComparatorChallenges/CoulombRadii.lean` (openai/math, Apache-2.0). The Thomas–Fermi coefficient
is characterized verbatim as in OpenAI's challenge `ComparatorChallenges/CoulombIonization.lean`.
The sector energy, the ionization energies and the half-electron radius are defined here.

`Statement` asserts:
1. two-sided universal bounds `c ≤ I₁(Z) ≤ C` on the first ionization energy, for every `Z ≥ 1`;
2. existence of a normalized ground state of every neutral atom;
3. two-sided universal bounds `c ≤ R(Ψ) ≤ C` on the half-electron radius of every normalized
   neutral ground state;
4. Thomas–Fermi asymptotics `I_m(Z) / m^{7/3} → a_TF` as `m → ∞` and `Z / m → ∞`.
-/

namespace AtomicIonization

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

/-! ### The model (verbatim from OpenAI's `CoulombRadii` challenge) -/

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := Fin n → Position
abbrev Spins (n : ℕ) := Fin n → Fin 2
abbrev Wavefunction (n : ℕ) := Spins n → Configuration n → ℂ
abbrev Gradient (n : ℕ) := Spins n → Fin n → Fin 3 → Configuration n → ℂ

def coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n :=
  Pi.single i (EuclideanSpace.single a 1)

def HasWeakGradient {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  ∀ σ i a (φ : Configuration n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ σ x) =
      -(∫ x, (φ x : ℂ) * g σ i a x)

def IsAntisymmetric {n : ℕ} (ψ : Wavefunction n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (σ : Spins n),
    (fun x : Configuration n => ψ (σ ∘ p) (x ∘ p)) =ᵐ[volume]
      (fun x => (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x)

def FormDomain {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  IsAntisymmetric ψ ∧ HasWeakGradient ψ g ∧
  (∀ σ, MemLp (ψ σ) 2 volume) ∧
  (∀ σ i a, MemLp (g σ i a) 2 volume) ∧
  (∀ σ i, Integrable (fun x : Configuration n => ‖x i‖⁻¹ * ‖ψ σ x‖ ^ 2)) ∧
  (∀ σ i j, i < j →
    Integrable (fun x : Configuration n => ‖x i - x j‖⁻¹ * ‖ψ σ x‖ ^ 2))

def normSquared {n : ℕ} (ψ : Wavefunction n) : ℝ :=
  ∑ σ : Spins n, ∫ x : Configuration n, ‖ψ σ x‖ ^ 2

def coulombPotential {n : ℕ} (Z : ℕ) (x : Configuration n) : ℝ :=
  -(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹) +
    ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), ‖x i - x j‖⁻¹

def energy {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) : ℝ :=
  (1 / 2 : ℝ) * (∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, ‖g σ i a x‖ ^ 2) +
  ∑ σ : Spins n, ∫ x : Configuration n, coulombPotential Z x * ‖ψ σ x‖ ^ 2

def IsNormalizedGroundState (Z : ℕ) (ψ : Wavefunction Z) : Prop :=
  ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
    ∀ (χ : Wavefunction Z) (h : Gradient Z),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h

def density {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) : ℝ :=
  (N + 1 : ℝ) * ∑ σ : Spins (N + 1),
    ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2

def exteriorMass {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, density ψ x

/-! ### Sector energies, ionization energies and the half-electron radius -/

/-- `E_Z(n) = inf σ(H_{n,Z})`, the infimum of the energy form over normalized vectors of the
form domain; `E_Z(0) = 0`. -/
def groundEnergy (Z n : ℕ) : ℝ :=
  if n = 0 then 0 else
    sInf {e : ℝ | ∃ (ψ : Wavefunction n) (g : Gradient n),
      FormDomain ψ g ∧ normSquared ψ = 1 ∧ energy Z ψ g = e}

/-- The generalized ionization energy `I_m(Z) = E_Z(Z - m) - E_Z(Z)`; `I_1(Z)` is the first
ionization energy of the neutral atom. -/
def ionizationEnergy (m Z : ℕ) : ℝ :=
  groundEnergy Z (Z - m) - groundEnergy Z Z

/-- `R(Ψ) = inf {r ≥ 0 : ∫_{|x|>r} ρ_Ψ ≤ 1/2}`, the radius containing all but an expected half
electron. -/
def halfRadius {N : ℕ} (ψ : Wavefunction (N + 1)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (1 / 2 : ℝ)}

/-! ### Thomas–Fermi coefficient (verbatim from OpenAI's `CoulombIonization` challenge) -/

def tfKinetic : ℝ := (3 / 10 : ℝ) * (3 * Real.pi ^ 2) ^ (2 / 3 : ℝ)

def directIntegrand (ρ : Position → ℝ) (p : Position × Position) : ℝ :=
  ρ p.1 * ρ p.2 / ‖p.1 - p.2‖

def TFAdmissible (M : ℝ) (ρ : Position → ℝ) : Prop :=
  (∀ᵐ x, 0 ≤ ρ x) ∧ Integrable ρ ∧ (∫ x, ρ x) = M ∧
  Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) ∧
  Integrable (fun x => ρ x / ‖x‖) ∧ Integrable (directIntegrand ρ)

def tfFunctional (Z : ℝ) (ρ : Position → ℝ) : ℝ :=
  tfKinetic * (∫ x, ρ x ^ (5 / 3 : ℝ)) - Z * (∫ x, ρ x / ‖x‖) +
    (1 / 2 : ℝ) * ∫ p, directIntegrand ρ p

def tfEnergy (Z M : ℝ) : ℝ :=
  sInf {e | ∃ ρ : Position → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}

def tfIonization (m Z : ℝ) : ℝ := tfEnergy Z (Z - m) - tfEnergy Z Z

/-- `a` is the Thomas–Fermi coefficient: `I_m^TF(Z) → a m^{7/3}` as `Z → ∞`, for every `m > 0`. -/
def TFCharacterization (a : ℝ) : Prop :=
  ∀ m : ℝ, 0 < m →
    Tendsto (tfIonization m) atTop (𝓝 (a * m ^ (7 / 3 : ℝ)))

/-! ### The statement -/

def Statement : Prop :=
  -- first ionization energy: universal two-sided bounds
  (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ Z : ℕ, 1 ≤ Z →
      c ≤ ionizationEnergy 1 Z ∧ ionizationEnergy 1 Z ≤ C) ∧
  -- every neutral atom has a normalized ground state
  (∀ N : ℕ, ∃ ψ : Wavefunction (N + 1), IsNormalizedGroundState (N + 1) ψ) ∧
  -- half-electron radius: universal two-sided bounds for every normalized neutral ground state
  (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ N : ℕ, ∀ ψ : Wavefunction (N + 1),
      IsNormalizedGroundState (N + 1) ψ → c ≤ halfRadius ψ ∧ halfRadius ψ ≤ C) ∧
  -- generalized ionization: Thomas–Fermi asymptotics as `m → ∞` and `Z / m → ∞`
  (∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧
    ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
      Tendsto m atTop atTop →
      Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
      Tendsto (fun j => ionizationEnergy (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
        atTop (𝓝 a))

end

end AtomicIonization
