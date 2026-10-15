# atomic-ionization-lean4

A Lean 4 formalization of uniform ionization bounds and generalized ionization asymptotics for the full nonrelativistic Coulomb atom with two electron spin states.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authorship and attribution](AUTHORS.md).
- **Mathematics:** OpenAI, *Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms* (2026), Theorem 1.2 and Corollary 1.3, and *Generalized ionization energies for full Coulomb atoms* (2026), Theorem 1.1. The manuscripts and the Lean libraries this formalization builds on are in [openai/math](https://github.com/openai/math).
- Developed with AI assistance; all proofs are verified by the Lean 4 kernel.

## Main result

`AtomicIonization.main_theorem : AtomicIonization.Statement`, in [Main.lean](AtomicIonization/Main.lean).

The statement is in [Challenge.lean](AtomicIonization/Challenge.lean), which imports only Mathlib. A nucleus of integer charge `Z ≥ 1` is fixed at the origin; `n` electrons with two spin states have kinetic energy `-Δ/2`, are attracted by the nucleus and repel each other, and their wavefunctions are antisymmetric in the joint space–spin variables. The energy `E_Z(n)` is the infimum of the Coulomb quadratic form over normalized vectors of the antisymmetric `H¹` form domain, with `E_Z(0) = 0`, and `I_m(Z) = E_Z(Z - m) - E_Z(Z)`. A normalized ground state of the neutral atom is a normalized minimizer of the form in the sector `n = Z`; its half-electron radius is `R(Ψ) = inf {r ≥ 0 : ∫_{|x|>r} ρ_Ψ ≤ 1/2}`, where `ρ_Ψ` is the spin-summed one-electron density. `Statement` asserts:

1. there are constants `0 < c ≤ C` with `c ≤ I₁(Z) ≤ C` for every integer `Z ≥ 1`;
2. every neutral atom has a normalized ground state;
3. there are constants `0 < c ≤ C` with `c ≤ R(Ψ) ≤ C` for every integer `Z ≥ 1` and every normalized ground state `Ψ` of the neutral atom;
4. there is `a_TF > 0`, characterized by `I_m^TF(Z) → a_TF m^{7/3}` as `Z → ∞` for the Thomas–Fermi ionization energies, such that `I_m(Z) / m^{7/3} → a_TF` whenever `m → ∞` and `Z / m → ∞` with integers `1 ≤ m < Z`.

The model (form domain, energy form, ground states, density, exterior mass) is copied verbatim from OpenAI's Comparator statement `CoulombRadii`, and the Thomas–Fermi characterization from its statement `CoulombIonization`.

The final theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. No proof in the repository uses `sorry` or an added axiom.

## Build and verify

Requirements: Git and [elan](https://github.com/leanprover/elan), with `lake` on `PATH`. Run from the repository root:

```sh
lake exe cache get
./scripts/verify.sh
```

The first command fetches the compiled Mathlib cache. The script builds the library, including the vendored OpenAI modules, and prints the axioms of the final theorem and of each package theorem ([Verification/Axioms.lean](Verification/Axioms.lean)). It fails if any of them uses `sorryAx` or an axiom other than the three above.

The checks of release v1.0.0 (fresh-clone build, kernel replay with `leanchecker --fresh`, Comparator with the nanoda kernel, and controls) are recorded in [docs/verification.md](docs/verification.md).

## Layout

[Blueprint/Main.lean](AtomicIonization/Blueprint/Main.lean) derives `Statement` from the package theorems `AtomicIonization.Blueprint.Packages.*`, whose statements are in [Blueprint/Interfaces.lean](AtomicIonization/Blueprint/Interfaces.lean).

| Package | Content | Module |
| --- | --- | --- |
| `groundEnergy_eq_formBottom` | sector energy = OpenAI's form bottom | [ModelBridge/GroundEnergyEqFormBottom](AtomicIonization/ModelBridge/GroundEnergyEqFormBottom.lean) |
| `groundEnergy_le` | sector energy is a lower bound for normalized trial states | [ModelBridge/GroundEnergyLe](AtomicIonization/ModelBridge/GroundEnergyLe.lean) |
| `joint_limit` | Thomas–Fermi joint limit, from OpenAI's `generalized_ionization` | [ModelBridge/JointLimit](AtomicIonization/ModelBridge/JointLimit.lean) |
| `ionization_upper` | `I₁(Z) ≤ C` (U, Prop 12.3) | [UpperBound/IonizationUpper](AtomicIonization/UpperBound/IonizationUpper.lean) |
| `binding` | `E_Z(n) < E_Z(n-1)` for `1 ≤ n ≤ Z` (U, Lemma 2.5) | [AtomicBinding/Binding](AtomicIonization/AtomicBinding/Binding.lean) |
| `groundState_exists` | ground states for `1 ≤ n ≤ Z` (U, Lemma 2.5) | [AtomicBinding/GroundState](AtomicIonization/AtomicBinding/GroundState.lean) |
| `ionization_gap` | `I₁(Z) ≥ c` for large `Z` (U, Prop 13.1) | [IonizationGap/Package](AtomicIonization/IonizationGap/Package.lean) |
| `exterior_tail` | exterior mass `≤ C/R` (U, Prop 14.1) | [ExteriorTail/Tail](AtomicIonization/ExteriorTail/Tail.lean) |
| `radius_lower_large` | `R(Ψ) ≥ c` for large `Z` (U, §12) | [HalfRadius/Large](AtomicIonization/HalfRadius/Large.lean) |
| `radius_bounds_fixed` | two-sided radius bounds for each fixed `Z` (U, §14) | [HalfRadius/Fixed](AtomicIonization/HalfRadius/Fixed.lean) |

Here U is *Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms*. The formal proofs follow the manuscript with some changes of route: the change of measure in Prop 14.1 is applied to a reweighted ground state, Prop 13.1 uses a smoothed multiplier, and the binding and fixed-charge radius steps use direct estimates in place of Newton's theorem and compactness.

[OAI/](OAI) holds OpenAI's libraries `CoulombRadii` and `CoulombIonization`, unchanged; see [THIRD_PARTY.md](THIRD_PARTY.md).
