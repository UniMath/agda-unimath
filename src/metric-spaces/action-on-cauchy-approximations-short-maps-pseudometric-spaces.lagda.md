# The action on Cauchy approximations of short maps between pseudometric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Short maps](metric-spaces.short-maps-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) act on
[cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
and induce a short map between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md).

## Definitions

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space A B)
  where

  map-cauchy-approximation-short-map-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space A →
    cauchy-approximation-Pseudometric-Space B
  map-cauchy-approximation-short-map-Pseudometric-Space (u , H) =
    ( map-short-map-Pseudometric-Space A B f ∘ u ,
      λ ε δ →
        is-short-map-short-map-Pseudometric-Space
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
  (f : short-map-Pseudometric-Space A B)
  where

  abstract
    preserves-neighborhoods-map-cauchy-approximation-short-map-Pseudometric-Space :
      is-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space A)
        ( cauchy-pseudocompletion-Pseudometric-Space B)
        ( map-cauchy-approximation-short-map-Pseudometric-Space A B f)
    preserves-neighborhoods-map-cauchy-approximation-short-map-Pseudometric-Space
      d x y Nxy α β =
      is-short-map-short-map-Pseudometric-Space A B f
        ( α +ℚ⁺ β +ℚ⁺ d)
        ( map-cauchy-approximation-Pseudometric-Space A x α)
        ( map-cauchy-approximation-Pseudometric-Space A y β)
        ( Nxy α β)

  short-map-cauchy-approximation-short-map-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  short-map-cauchy-approximation-short-map-Pseudometric-Space =
    ( map-cauchy-approximation-short-map-Pseudometric-Space A B f ,
      preserves-neighborhoods-map-cauchy-approximation-short-map-Pseudometric-Space)
```
