# Products of pullbacks

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.products-pullbacks
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types funext
open import foundation.inhabited-types funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.pullbacks funext univalence truncations
open import foundation.standard-pullbacks funext
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universal-property-pullbacks funext
```

</details>

## Idea

Given two
[commuting squares of maps](foundation-core.commuting-squares-of-maps.md),

```text
    C ------> B                  C' -----> B'
    |         |                  |         |
    |         |  g     and       |         | g'
    ∨         ∨                  ∨         ∨
    A ------> X                  A' -----> X'
         f                            f'
```

then their product

```text
  C × C' ----> B × B'
    |            |
    |            | g × g'
    ∨            ∨
  A × A' ----> X × X'
         f × f'
```

is a [pullback](foundation-core.pullbacks.md) if each factor is. Conversely, if
the product is a pullback and the standard pullback of each factor is inhabited,
then each factor is also a pullback.

## Definitions

### Product cones

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  product-cone :
    cone f g C → cone f' g' C' →
    cone (map-product f f') (map-product g g') (C × C')
  pr1 (product-cone (p , q , H) (p' , q' , H')) = map-product p p'
  pr1 (pr2 (product-cone (p , q , H) (p' , q' , H'))) = map-product q q'
  pr2 (pr2 (product-cone (p , q , H) (p' , q' , H'))) = htpy-map-product H H'
```

## Properties

### Computing the standard pullback of a product

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  map-product-cone-standard-pullback :
    (standard-pullback f g) × (standard-pullback f' g') →
    standard-pullback (map-product f f') (map-product g g')
  map-product-cone-standard-pullback =
    ( tot
      ( λ t →
        ( tot (λ s → eq-pair')) ∘
        ( map-interchange-Σ-Σ (λ y p y' → f' (pr2 t) ＝ g' y')))) ∘
    ( map-interchange-Σ-Σ (λ x t x' → Σ B' (λ y' → f' x' ＝ g' y')))

  abstract
    is-equiv-map-product-cone-standard-pullback :
      is-equiv map-product-cone-standard-pullback
    is-equiv-map-product-cone-standard-pullback =
      is-equiv-comp
        ( tot (λ t → tot (λ s → eq-pair') ∘ map-interchange-Σ-Σ _))
        ( map-interchange-Σ-Σ _)
        ( is-equiv-map-interchange-Σ-Σ _)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ t →
            is-equiv-comp
              ( tot (λ s → eq-pair'))
              ( map-interchange-Σ-Σ (λ y p y' → f' (pr2 t) ＝ g' y'))
              ( is-equiv-map-interchange-Σ-Σ _)
              ( is-equiv-tot-is-fiberwise-equiv
                ( λ s →
                  is-equiv-eq-pair (map-product f f' t) (map-product g g' s)))))

  compute-product-standard-pullback :
    (standard-pullback f g) × (standard-pullback f' g') ≃
    standard-pullback (map-product f f') (map-product g g')
  compute-product-standard-pullback =
    ( map-product-cone-standard-pullback ,
      is-equiv-map-product-cone-standard-pullback)
```

### The gap map of the standard pullback of a product computes as a product of gap maps

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  triangle-map-product-cone-standard-pullback :
    (c : cone f g C) (c' : cone f' g' C') →
    ( gap (map-product f f') (map-product g g') (product-cone f g f' g' c c')) ~
    ( ( map-product-cone-standard-pullback f g f' g') ∘
      ( map-product (gap f g c) (gap f' g' c')))
  triangle-map-product-cone-standard-pullback c c' = refl-htpy
```

### Products of pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  abstract
    is-pullback-product-is-pullback :
      (c : cone f g C) (c' : cone f' g' C') →
      is-pullback f g c →
      is-pullback f' g' c' →
      is-pullback
        ( map-product f f')
        ( map-product g g')
        ( product-cone f g f' g' c c')
    is-pullback-product-is-pullback c c' is-pb-c is-pb-c' =
      is-equiv-left-map-triangle
        ( gap
          ( map-product f f')
          ( map-product g g')
          ( product-cone f g f' g' c c'))
        ( map-product-cone-standard-pullback f g f' g')
        ( map-product (gap f g c) (gap f' g' c'))
        ( triangle-map-product-cone-standard-pullback f g f' g' c c')
        ( is-equiv-map-product (gap f g c) (gap f' g' c') is-pb-c is-pb-c')
        ( is-equiv-map-product-cone-standard-pullback f g f' g')
```

### Products of cones satisfying the universal property of pullbacks satisfy the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C')
  where

  universal-property-pullback-product-universal-property-pullback :
    universal-property-pullback f g c →
    universal-property-pullback f' g' c' →
    universal-property-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c')
  universal-property-pullback-product-universal-property-pullback H H' =
    universal-property-pullback-is-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c')
      ( is-pullback-product-is-pullback f g f' g' c c'
        ( is-pullback-universal-property-pullback f g c H)
        ( is-pullback-universal-property-pullback f' g' c' H'))
```

### If the product is a pullback and the standard pullback of each factor is inhabited then both factors are pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  (c : cone f g C) (c' : cone f' g' C')
  where

  abstract
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product' :
      is-pullback
        ( map-product f f')
        ( map-product g g')
        ( product-cone f g f' g' c c') →
      standard-pullback f' g' →
      is-pullback f g c
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'
      H t =
      is-equiv-left-factor-is-equiv-map-product'
        ( gap f g c)
        ( gap f' g' c')
        ( t)
        ( is-equiv-top-map-triangle
          ( gap
            ( map-product f f')
            ( map-product g g')
            ( product-cone f g f' g' c c'))
          ( map-product-cone-standard-pullback f g f' g')
            ( map-product (gap f g c) (gap f' g' c'))
            ( triangle-map-product-cone-standard-pullback f g f' g' c c')
            ( is-equiv-map-product-cone-standard-pullback f g f' g')
            ( H))

  abstract
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product :
      is-pullback
        ( map-product f f')
        ( map-product g g')
        ( product-cone f g f' g' c c') →
      is-inhabited (standard-pullback f' g') →
      is-pullback f g c
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product
      H =
      rec-trunc-Prop
        ( is-pullback-Prop f g c)
        ( is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'
          ( H))

  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product' :
    is-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c') →
    C' →
    is-pullback f g c
  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product' H t =
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'
      ( H)
      ( gap f' g' c' t)

  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product :
    is-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c') →
    is-inhabited C' →
    is-pullback f g c
  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product H =
      rec-trunc-Prop
        ( is-pullback-Prop f g c)
        ( is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product'
          ( H))

  abstract
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product' :
      is-pullback
        ( map-product f f')
        ( map-product g g')
        ( product-cone f g f' g' c c') →
      standard-pullback f g →
      is-pullback f' g' c'
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'
      H t =
      is-equiv-right-factor-is-equiv-map-product'
        ( gap f g c)
        ( gap f' g' c')
        ( t)
        ( is-equiv-top-map-triangle
          ( gap
            ( map-product f f')
            ( map-product g g')
            ( product-cone f g f' g' c c'))
          ( map-product-cone-standard-pullback f g f' g')
          ( map-product (gap f g c) (gap f' g' c'))
          ( triangle-map-product-cone-standard-pullback f g f' g' c c')
          ( is-equiv-map-product-cone-standard-pullback f g f' g')
          ( H))

  abstract
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product :
      is-pullback
        ( map-product f f')
        ( map-product g g')
        ( product-cone f g f' g' c c') →
      is-inhabited (standard-pullback f g) →
      is-pullback f' g' c'
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product
      H =
      rec-trunc-Prop
        ( is-pullback-Prop f' g' c')
        ( is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'
          ( H))

  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product' :
    is-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c') →
    C →
    is-pullback f' g' c'
  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product' H t =
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'
      ( H)
      ( gap f g c t)

  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product :
    is-pullback
      ( map-product f f')
      ( map-product g g')
      ( product-cone f g f' g' c c') →
    is-inhabited C →
    is-pullback f' g' c'
  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product H =
      rec-trunc-Prop
        ( is-pullback-Prop f' g' c')
        ( is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product'
          ( H))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
