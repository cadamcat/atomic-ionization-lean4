# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorems were proved by OpenAI, in the papers [*Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms*](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Uniform-excess-charge-for-Coulomb-molecules-and-the-outer-radius-of-neutral-atoms-September-24-2026/paper.pdf) and [*Generalized ionization energies for full Coulomb atoms*](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf) (2026). This repository formalizes them; it does not claim a new mathematical solution. The formal proof follows the papers, with the changes of route described in the README, and uses OpenAI's Lean libraries for the many-electron form domain, the spectral and variational theory of the atom and the generalized ionization asymptotics.

The author planned, directed and reviewed the work, using AI coding assistants; all proofs and their dependencies are checked by the Lean kernel.

The project uses Mathlib and OpenAI's `openai/math` library, whose `CoulombRadii` and `CoulombIonization` directories are included unchanged under `OAI/`. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md).
