# Functorial action on isometries of Cauchy pseudocompletions of pseudometric spaces

```agda
module metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces where
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
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Isometries](metric-spaces.isometries-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) act on
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
and induce an isometry between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md).

It is the
{{#concept "functorial action" Disambiguation="of Cauchy pseudocompletions on isometries between pseudometric spaces" Agda=isometry-cauchy-pseudocompletion-Pseudometric-Space}}
of Cauchy pseudocompletions on isometries between pseudometric spaces.

## Definitions

### The action on isometries of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    map-short-map-cauchy-pseudocompletion-Pseudometric-Space A B
      ( short-map-isometry-Pseudometric-Space A B f)
```

## Properties

### The action on isometries is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where abstract

  preserves-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
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
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f x)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f y)
  preserves-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space A B f)

  reflects-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : cauchy-approximation-Pseudometric-Space A) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( d)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f x)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f y) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( d)
      ( x)
      ( y)
  reflects-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
    d x y Nxy α β =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( f)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( map-cauchy-approximation-Pseudometric-Space A x α)
      ( map-cauchy-approximation-Pseudometric-Space A y β)
      ( Nxy α β)

  is-isometry-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f)
  is-isometry-map-isometry-cauchy-pseudocompletion-Pseudometric-Space d x y =
    ( ( preserves-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( d)
        ( x)
        ( y)))

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space A)
      ( cauchy-pseudocompletion-Pseudometric-Space B)
  isometry-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f ,
      is-isometry-map-isometry-cauchy-pseudocompletion-Pseudometric-Space A B f)
```
