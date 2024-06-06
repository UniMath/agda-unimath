# Factorizations of maps into global function classes

```agda
module orthogonal-factorization-systems.factorizations-of-maps-global-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.factorizations-of-maps-function-classes
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.global-function-classes
```

</details>

## Idea

A **factorization into
[global function classes](orthogonal-factorization-systems.global-function-classes.md)
classes `L` and `R`** of a map `f : A → B` is a pair of maps `l : A → X` and
`r : X → B`, where `l ∈ L` and `r ∈ R`, such that their composite `r ∘ l` is
`f`.

```text
         X
        ∧ ╲
 L ∋ l ╱   ╲ r ∈ R
      ╱     ∨
    A ─────> B
        f
```

## Definitions

### The predicate of being a factorization into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} (f : A → B)
  (F : factorization l3 f)
  where

  is-global-function-class-factorization-Prop : Prop (βL l1 l3 ⊔ βR l3 l2)
  is-global-function-class-factorization-Prop =
    is-function-class-factorization-Prop
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  is-global-function-class-factorization : UU (βL l1 l3 ⊔ βR l3 l2)
  is-global-function-class-factorization =
    type-Prop is-global-function-class-factorization-Prop

  is-prop-is-global-function-class-factorization :
    is-prop is-global-function-class-factorization
  is-prop-is-global-function-class-factorization =
    is-prop-type-Prop is-global-function-class-factorization-Prop

  is-in-left-class-left-map-is-global-function-class-factorization :
    is-global-function-class-factorization →
    is-in-global-function-class L (left-map-factorization F)
  is-in-left-class-left-map-is-global-function-class-factorization =
    is-in-left-class-left-map-is-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  is-in-right-class-right-map-is-global-function-class-factorization :
    is-global-function-class-factorization →
    is-in-global-function-class R (right-map-factorization F)
  is-in-right-class-right-map-is-global-function-class-factorization =
    is-in-right-class-right-map-is-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  left-class-map-is-global-function-class-factorization :
    is-global-function-class-factorization →
    type-global-function-class L A (image-factorization F)
  left-class-map-is-global-function-class-factorization =
    left-class-map-is-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  right-class-map-is-global-function-class-factorization :
    is-global-function-class-factorization →
    type-global-function-class R (image-factorization F) B
  right-class-map-is-global-function-class-factorization =
    right-class-map-is-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)
```

### The type of factorizations into global function classes

```agda
global-function-class-factorization :
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B) →
  UU (βL l1 l3 ⊔ βR l3 l2 ⊔ l1 ⊔ l2 ⊔ lsuc l3)
global-function-class-factorization L R l3 =
  function-class-factorization {l3 = l3}
    ( function-class-global-function-class L)
    ( function-class-global-function-class R)

module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  (F : global-function-class-factorization L R l3 f)
  where

  factorization-global-function-class-factorization : factorization l3 f
  factorization-global-function-class-factorization =
    factorization-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  is-global-function-class-factorization-global-function-class-factorization :
    is-global-function-class-factorization L R f
      ( factorization-global-function-class-factorization)
  is-global-function-class-factorization-global-function-class-factorization =
    is-function-class-factorization-function-class-factorization
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)
      ( F)

  image-global-function-class-factorization : UU l3
  image-global-function-class-factorization =
    image-factorization factorization-global-function-class-factorization

  left-map-global-function-class-factorization :
    A → image-global-function-class-factorization
  left-map-global-function-class-factorization =
    left-map-factorization factorization-global-function-class-factorization

  right-map-global-function-class-factorization :
    image-global-function-class-factorization → B
  right-map-global-function-class-factorization =
    right-map-factorization factorization-global-function-class-factorization

  is-factorization-global-function-class-factorization :
    is-factorization f
      ( right-map-global-function-class-factorization)
      ( left-map-global-function-class-factorization)
  is-factorization-global-function-class-factorization =
    is-factorization-factorization
      ( factorization-global-function-class-factorization)

  is-in-left-class-left-map-global-function-class-factorization :
    is-in-global-function-class L left-map-global-function-class-factorization
  is-in-left-class-left-map-global-function-class-factorization =
    is-in-left-class-left-map-is-global-function-class-factorization L R f
      ( factorization-global-function-class-factorization)
      ( is-global-function-class-factorization-global-function-class-factorization)

  is-in-right-class-right-map-global-function-class-factorization :
    is-in-global-function-class R right-map-global-function-class-factorization
  is-in-right-class-right-map-global-function-class-factorization =
    is-in-right-class-right-map-is-global-function-class-factorization L R f
      ( factorization-global-function-class-factorization)
      ( is-global-function-class-factorization-global-function-class-factorization)

  left-class-map-global-function-class-factorization :
    type-global-function-class L A image-global-function-class-factorization
  left-class-map-global-function-class-factorization =
    left-class-map-is-global-function-class-factorization L R f
      ( factorization-global-function-class-factorization)
      ( is-global-function-class-factorization-global-function-class-factorization)

  right-class-map-global-function-class-factorization :
    type-global-function-class R image-global-function-class-factorization B
  right-class-map-global-function-class-factorization =
    right-class-map-is-global-function-class-factorization L R f
      ( factorization-global-function-class-factorization)
      ( is-global-function-class-factorization-global-function-class-factorization)
```
