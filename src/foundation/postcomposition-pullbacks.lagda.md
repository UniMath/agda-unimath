# Postcomposition of pullbacks

```agda
module foundation.postcomposition-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.standard-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

Given a [pullback](foundation-core.pullbacks.md) square

```text
         f'
    C -------> B
    | ⌟        |
  g'|          | g
    ∨          ∨
    A -------> X
         f
```

then the exponentiated square given by
[postcomposition](foundation-core.postcomposition-functions.md)

```text
                f' ∘ -
      (T → C) ---------> (T → B)
         |                  |
  g' ∘ - |                  | g ∘ -
         |                  |
         ∨                  ∨
      (T → A) ---------> (T → X)
                f ∘ -
```

is a pullback square for any type `T`.

## Definitions

### Postcomposition cones

```agda
postcomp-cone :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (postcomp T f) (postcomp T g) (T → C)
postcomp-cone T f g c =
  ( postcomp T (vertical-map-cone f g c) ,
    postcomp T (horizontal-map-cone f g c) ,
    htpy-postcomp T (coherence-square-cone f g c))
```

## Properties

### The standard pullback of a postcomposition exponential computes as the type of cones

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4)
  where

  map-standard-pullback-postcomp :
    standard-pullback (postcomp T f) (postcomp T g) → cone f g T
  map-standard-pullback-postcomp = tot (λ _ → tot (λ _ → htpy-eq))

  abstract
    is-equiv-map-standard-pullback-postcomp :
      is-equiv map-standard-pullback-postcomp
    is-equiv-map-standard-pullback-postcomp =
      is-equiv-tot-is-fiberwise-equiv
        ( λ p → is-equiv-tot-is-fiberwise-equiv (λ q → funext (f ∘ p) (g ∘ q)))

  compute-standard-pullback-postcomp :
    standard-pullback (postcomp T f) (postcomp T g) ≃ cone f g T
  compute-standard-pullback-postcomp =
    ( map-standard-pullback-postcomp ,
      is-equiv-map-standard-pullback-postcomp)
```

### The precomposition action on cones computes as the gap map of a postcomposition cone

```agda
triangle-map-standard-pullback-postcomp :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  coherence-triangle-maps
    ( cone-map f g c {T})
    ( map-standard-pullback-postcomp f g T)
    ( gap (postcomp T f) (postcomp T g) (postcomp-cone T f g c))
triangle-map-standard-pullback-postcomp T f g c h =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber
      ( inv (is-section-eq-htpy (coherence-square-cone f g c ·r h))))
```

### Pullbacks are closed under postcomposition exponentiation

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-pullback-postcomp-is-pullback :
      is-pullback f g c → {l5 : Level} (T : UU l5) →
      is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)
    is-pullback-postcomp-is-pullback is-pb-c T =
      is-equiv-top-map-triangle _ _ _
        ( triangle-map-standard-pullback-postcomp T f g c)
        ( is-equiv-map-standard-pullback-postcomp f g T)
        ( universal-property-pullback-is-pullback f g c is-pb-c T)

  abstract
    is-pullback-is-pullback-postcomp :
      ( {l5 : Level} (T : UU l5) →
        is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)) →
      is-pullback f g c
    is-pullback-is-pullback-postcomp is-pb-postcomp =
      is-pullback-universal-property-pullback f g c
        ( λ T →
          is-equiv-left-map-triangle _ _ _
            ( triangle-map-standard-pullback-postcomp T f g c)
            ( is-pb-postcomp T)
            ( is-equiv-map-standard-pullback-postcomp f g T))
```

### Cones satisfying the universal property of pullbacks are closed under postcomposition exponentiation

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (T : UU l5)
  where

  universal-property-pullback-postcomp-universal-property-pullback :
    universal-property-pullback f g c →
    universal-property-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( postcomp-cone T f g c)
  universal-property-pullback-postcomp-universal-property-pullback H =
    universal-property-pullback-is-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( postcomp-cone T f g c)
      ( is-pullback-postcomp-is-pullback f g c
        ( is-pullback-universal-property-pullback f g c H)
        ( T))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
