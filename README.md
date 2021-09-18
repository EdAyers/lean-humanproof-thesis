
Implementation of the HumanProof prover system, accompanying https://edayers.com/thesis.

Please note that the system is a prototype.

# Installation

## Install Lean 3

Make sure that you have installed `elan`, Visual Studio Code and `leanproject`.
Up-to-date information on how to do this can be found [on the leanprover-community website](https://leanprover-community.github.io/get_started.html#regular-install).

## Set up the project

```
git clone https://github.com/EdAyers/lean-humanproof-thesis.git
cd lean-humanproof-thesis
leanpkg configure
leanproject get-mathlib-cache
leanpkg build
```

Then open the project in VSCode to view the examples.

# Usage

The analysis examples used in the thesis can be found in `examples/analysis.lean`.
The equational reasoning examples were generated from a different project https://github.com/EdAyers/lean-subtask.
At the time of submission I did not integrate these two modules in to a single system to the extent that I am confident to release the code.

