# The action of isometries on Cauchy approximations in pseudometric spaces

```agda
module metric-spaces.action-of-isometries-on-cauchy-approximations-pseudometric-spaces where
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

open import metric-spaces.action-of-short-maps-on-cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
```

</details>

## Idea

[Isometries](metric-spaces.isometries-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) act on their
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
and induce an isometry between their
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md).

## Definitions

### The action of isometries on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  map-cauchy-approximation-isometry-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space A →
    cauchy-approximation-Pseudometric-Space B
  map-cauchy-approximation-isometry-Pseudometric-Space =
    map-cauchy-approximation-short-function-Pseudometric-Space
      ( A)
      ( B)
      ( short-isometry-Pseudometric-Space A B f)
```

## Properties

### The action of isometries on Cauchy approximations is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where abstract

  preserves-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : cauchy-approximation-Pseudometric-Space A) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( d)
      ( x)
      ( y) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( d)
      ( map-cauchy-approximation-isometry-Pseudometric-Space A B f x)
      ( map-cauchy-approximation-isometry-Pseudometric-Space A B f y)
  preserves-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space =
    preserves-neighborhoods-map-cauchy-approximation-short-function-Pseudometric-Space
      ( A)
      ( B)
      ( short-isometry-Pseudometric-Space A B f)

  reflects-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : cauchy-approximation-Pseudometric-Space A) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( d)
      ( map-cauchy-approximation-isometry-Pseudometric-Space A B f x)
      ( map-cauchy-approximation-isometry-Pseudometric-Space A B f y) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( d)
      ( x)
      ( y)
  reflects-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space
    d x y Nxy α β =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( f)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( map-cauchy-approximation-Pseudometric-Space A x α)
      ( map-cauchy-approximation-Pseudometric-Space A y β)
      ( Nxy α β)

  is-isometry-map-cauchy-approximation-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( map-cauchy-approximation-isometry-Pseudometric-Space A B f)
  is-isometry-map-cauchy-approximation-isometry-Pseudometric-Space d x y =
    ( ( preserves-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-cauchy-approximation-isometry-Pseudometric-Space
        ( d)
        ( x)
        ( y)))

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  isometry-map-cauchy-approximation-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  isometry-map-cauchy-approximation-isometry-Pseudometric-Space =
    ( map-cauchy-approximation-isometry-Pseudometric-Space A B f ,
      is-isometry-map-cauchy-approximation-isometry-Pseudometric-Space A B f)
```
