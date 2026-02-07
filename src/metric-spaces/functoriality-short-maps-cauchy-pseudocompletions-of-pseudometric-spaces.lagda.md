# Functorial action on short maps of Cauchy pseudocompletions of pseudometric spaces

```agda
module metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces where
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
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Short maps](metric-spaces.short-maps-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) act on
[cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
and induce a short map between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md).

## Definitions

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space A B)
  where

  map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  map-short-map-cauchy-pseudocompletion-Pseudometric-Space (u , H) =
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
    preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
      is-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space A)
        ( cauchy-pseudocompletion-Pseudometric-Space B)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space A B f)
    preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
      d x y Nxy α β =
      is-short-map-short-map-Pseudometric-Space A B f
        ( α +ℚ⁺ β +ℚ⁺ d)
        ( map-cauchy-approximation-Pseudometric-Space A x α)
        ( map-cauchy-approximation-Pseudometric-Space A y β)
        ( Nxy α β)

  short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  short-map-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space A B f ,
      preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

### The action of short maps on Cauchy approximations preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f g : short-map-Pseudometric-Space A B)
  (f~g : htpy-map-short-map-Pseudometric-Space A B f g)
  where

  htpy-map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    htpy-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( short-map-cauchy-pseudocompletion-Pseudometric-Space A B f)
      ( short-map-cauchy-pseudocompletion-Pseudometric-Space A B g)
  htpy-map-short-map-cauchy-pseudocompletion-Pseudometric-Space u =
    eq-htpy-cauchy-approximation-Pseudometric-Space B
      ( f~g ∘ map-cauchy-approximation-Pseudometric-Space A u)
```

### The action of short maps on Cauchy approximations is natural w.r.t. the unit map

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space A B)
  where

  coh-square-map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space A B f ∘
      map-unit-cauchy-pseudocompletion-Pseudometric-Space A) ~
    ( map-unit-cauchy-pseudocompletion-Pseudometric-Space B ∘
      map-short-map-Pseudometric-Space A B f)
  coh-square-map-short-map-cauchy-pseudocompletion-Pseudometric-Space x =
    eq-htpy-cauchy-approximation-Pseudometric-Space B refl-htpy
```
