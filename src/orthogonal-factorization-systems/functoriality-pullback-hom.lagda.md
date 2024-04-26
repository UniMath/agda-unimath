# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.bicomposition-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.retracts-of-maps
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.

## Definitions

### The functorial action on morphisms of cospan diagrams of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {l1' l2' l3' l4' : Level}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-hom-cospan-diagram-pullback-hom :
    hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g') →
    hom-arrow f g → hom-arrow f' g'
  map-hom-cospan-diagram-pullback-hom =
    map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')
      ( cone-hom-arrow-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f' g')
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f' g')
```

## Properties

### The functorial action of the pullback-hom preserves identities

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-cospan-diagram-pullback-hom :
    map-hom-cospan-diagram-pullback-hom f g f g
      ( id-hom-cospan-diagram (cospan-diagram-pullback-hom f g)) ~ id
  preserves-id-map-hom-cospan-diagram-pullback-hom =
    preserves-id-map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
```

## The functorial action of the pullback-hom preserves composition

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  preserves-comp-map-hom-cospan-diagram-pullback-hom :
    (h : hom-cospan-diagram
      ( cospan-diagram-pullback-hom f' g')
      ( cospan-diagram-pullback-hom f'' g'')) →
    (h' : hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')) →
    map-hom-cospan-diagram-pullback-hom f g f'' g''
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( h)
        ( h')) ~
    map-hom-cospan-diagram-pullback-hom f' g' f'' g'' h ∘
    map-hom-cospan-diagram-pullback-hom f g f' g' h'
  preserves-comp-map-hom-cospan-diagram-pullback-hom =
    preserves-comp-map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')
      ( cospan-diagram-pullback-hom f'' g'')
      ( cone-hom-arrow-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f' g')
      ( cone-hom-arrow-pullback-hom f'' g'')
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f' g')
      ( is-pullback-cone-hom-arrow-pullback-hom f'' g'')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
