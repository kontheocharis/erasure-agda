# Formalisation of the paper "Type Theory with Erasure"

[Paper link (Draft)](cthe.me/erasure-sogat.pdf)

## Contents

| File | Description |
|------|-------------|
| [Utils.agda](Utils.agda) | Utilities for observational equality using Agda's definitionally proof irrelevant propositions. This saves a lot of headache of dealing with coherence conditions compared to using inductively-defined equality in Set. |
| [Mode.agda](Mode.agda) | The erasure mode type, along with mode multiplication and algebraic laws. |

### Theories

| File | Description |
|------|-------------|
| [Theories/TT.agda](Theories/TT.agda) | SOGAT of type theory with Π-types, a Tarski universe, and natural numbers. |
| [Theories/TTwE.agda](Theories/TTwE.agda) | SOGAT of type theory with erasure (TT₀ in the paper) with Π-types, a Tarski universe, and natural numbers |
| [Theories/CwF.agda](Theories/CwF.agda) | GAT of type theory with Π types and type-in-type universe. |
| [Theories/CwFwE.agda](Theories/CwFwE.agda) | GAT of type theory with erasure (TT₀^fo in the paper), with Π types and type-in-type universe. |
| [Theories/LC.agda](Theories/LC.agda) | SOGAT of untyped lambda calculus. |

### Models — First-Order

| File | Description |
|------|-------------|
| [Models/FO/FamSet.agda](Models/FO/FamSet.agda) | Families-of-sets model of CwFwE, explicitly in Set. |
| [Models/FO/Zeroing.agda](Models/FO/Zeroing.agda) | First-order zeroing model interpreting all modes as erased, as well as a proof by induction that types and erased terms 'need nothing' (Theorem 7 in the paper). |
| [Models/FO/ExtractionCorrectness.agda](Models/FO/ExtractionCorrectness.agda) | Extraction model with a logical relation establishing semantic correctness of extracted code (Theorems 18-20). This whole file lives in Psh(λ), see top comment. |

### Models (second-order)

We include these here because it is much easier to write them than the
first-order models and perhaps more informative.

| File | Description |
|------|-------------|
| [Models/SO/Extraction.agda](Models/SO/Extraction.agda) | Extraction model mapping TTwE to untyped lambda calculus. Should be thought of as living in Psh(λ), rather than a SOGAT morphism because we use ⊥ for the erasure marker #. |
| [Models/SO/Zeroing.agda](Models/SO/Zeroing.agda) | Zeroing model interpreting all modes as erased. |
| [Models/SO/Conservativity.agda](Models/SO/Conservativity.agda) | Bidirectional interpretations between TT₀ and TT. |


## Some naming differences:

- TT₀ in the paper is called `TTwE` here
- TT₀ᶠᵒ  in the paper is called `CwFwE` here.

## Remaining `TODO`s:

- Derive first-order version of the zeroing Π structure (`Models/FO/Zeroing.agda`)
- Derive second-order version of the zeroing Nat eliminator computation rules
  (`Theories/TTwE.agda`); leads to holes in `Models/SO/Zeroing.agda` and
  `Models/SO/Conservativity.agda`
- Formalise the conservativity theorems (10 and 11) in first-order form:
  quite a straightforward induction with motives of the form `⌞⌜Γ⌝⌟ ≡ Γ`.
