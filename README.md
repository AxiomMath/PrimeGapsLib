[![](logo.svg)](https://axiommath.ai/)

# PrimeGapsLib

Public Lean library for formalizations related to prime gaps, maintained by Axiom Math.

## Dependencies

This repository depends on [an internal fork of PrimeNumberTheoremAnd](https://github.com/AxiomMath/PrimeNumberTheoremAnd) (original [here](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)), changed to use the module system.

## Structure

* [PrimeGaps](PrimeGaps/): the main library combining [PrimeGapsTheory](PrimeGapsTheory/) and [PrimeGapsCert](PrimeGapsCert/).
* [PrimeGapsTheory](PrimeGapsTheory/): the main formalization excluding large numerical computations, which builds quickly.
* [PrimeGapsCert](PrimeGapsCert/): large numerical computations that might take a long time to build.

## Main Results

1. The Bombieri–Vinogradov theorem implies prime gaps bounded by 246 infinitely often, located in [PrimeGaps.Bounded246](PrimeGaps/Bounded246.lean).
2. The Bombieri–Vinogradov theorem implies prime gaps bounded by 600 infinitely often, located in [PrimeGapsTheory.Endgame.Main](PrimeGapsTheory/Endgame/Main.lean).
3. The Bombieri–Vinogradov theorem and existence of certificate imply prime gaps bounded by 246 infinitely often, located in [PrimeGapsTheory.Gap246.Endgame.Main](PrimeGapsTheory/Gap246/Endgame/Main.lean).

Formal versions of these statements can be found in the formal challenge described in [§Comparator](#comparator).

## Comparator

A formal challenge that is self-contained and only depends on Mathlib is located in [Comparator.Challenge](Comparator/Challenge.lean). It contains statement 1 of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```
Beware that this can take hours.

The proofs of statements 2 and 3 of [§Main Results](#main-results) compile much faster, so we also included a formal challenge for them in [Comparator.ChallengeFast](Comparator/ChallengeFast.lean). To verify this repository against this challenge file, run the following command:
```
lake env comparator Comparator/comparator_fast.json
```
This should only takes minutes.
