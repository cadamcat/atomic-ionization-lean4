# Verification record

Checks of release v1.0.0, commit `d083b8d861d96980b154be3945696e9d277e53c2`, on 2026-10-14. The run started from a fresh clone of this repository at the tag, with the published `lake-manifest.json`, fetched the Mathlib cache and used 12 threads on the author's Mac. The vendored OpenAI modules were built from source.

| Check | Command | Result |
| --- | --- | --- |
| Build | `lake build` | exit 0, 9978 jobs |
| Axioms | `lake env lean Verification/Axioms.lean` | `'AtomicIonization.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`, and the same three for every package theorem |
| Kernel replay | `lake env leanchecker --fresh AtomicIonization.Main` | exit 0 |
| Comparator | challenge: [AtomicIonization/Challenge.lean](../AtomicIonization/Challenge.lean) with `AtomicIonization.main_theorem : AtomicIonization.Statement` added as `sorry`; `definition_names` empty; nanoda enabled | exit 0: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" |

Comparator compares the final theorem's type and every definition of `Challenge.lean` (Mathlib definitions only) that it unfolds to with the library's. With `definition_names` empty, the bodies of those definitions are compared too.

Tool versions: Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`, lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`. Comparator ran with its development `fake-landrun.sh`, not the Landrun sandbox.

## Controls

- nanoda accepted a correct proof and rejected a proof by `sorry` (exit 1) and an export with a tampered numeral (exit 101).
- With the half-electron radius threshold in the challenge changed from `1 / 2` to `1 / 3`, Comparator rejected the solution: "Const does not match between challenge and target 'AtomicIonization.Statement'".
- `scripts/verify.sh` fails (exit 2) when a theorem proved by `sorry` is added to the list of axiom reports.
