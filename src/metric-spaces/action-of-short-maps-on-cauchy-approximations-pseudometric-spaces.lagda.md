# The action on Cauchy approximations of short maps between pseudometric spaces

```agda
module metric-spaces.action-of-short-maps-on-cauchy-approximations-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
```

</details>

## Idea

[Short maps](metric-spaces.short-functions-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) act on their
[cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
and induce a short map between their
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md).

## Definitions

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-function-Pseudometric-Space A B)
  where

  map-cauchy-approximation-short-function-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space A →
    cauchy-approximation-Pseudometric-Space B
  map-cauchy-approximation-short-function-Pseudometric-Space (u , H) =
    ( map-short-function-Pseudometric-Space A B f ∘ u ,
      λ ε δ →
        is-short-map-short-function-Pseudometric-Space
          ( A)
          ( B)
          ( f)
          ( ε +ℚ⁺ δ)
          ( u ε)
          ( u δ)
          ( H ε δ))
```

## Properties

### The action of short maps on Cauchy approximations is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-function-Pseudometric-Space A B)
  where

  preserves-neighborhoods-map-cauchy-approximation-short-function-Pseudometric-Space :
    is-short-function-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( map-cauchy-approximation-short-function-Pseudometric-Space A B f)
  preserves-neighborhoods-map-cauchy-approximation-short-function-Pseudometric-Space
    d x y Nxy α β =
    is-short-map-short-function-Pseudometric-Space A B f
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( map-cauchy-approximation-Pseudometric-Space A x α)
      ( map-cauchy-approximation-Pseudometric-Space A y β)
      ( Nxy α β)

  short-map-cauchy-approximation-short-function-Pseudometric-Space :
    short-function-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  short-map-cauchy-approximation-short-function-Pseudometric-Space =
    ( map-cauchy-approximation-short-function-Pseudometric-Space A B f ,
      preserves-neighborhoods-map-cauchy-approximation-short-function-Pseudometric-Space)
```
