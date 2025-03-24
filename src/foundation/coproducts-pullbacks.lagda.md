# Coproducts of pullbacks

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.coproducts-pullbacks
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams funext
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types funext univalence truncations
open import foundation.functoriality-coproduct-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.standard-pullbacks funext
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.pullbacks funext
open import foundation-core.retractions
open import foundation-core.sections
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
    A ------> X                  A' -----> X',
         f                            f'
```

then their coproduct

```text
  C + C' ----> B + B'
    |            |
    |            | g + g'
    ∨            ∨
  A + A' ----> X + X'
         f + f'
```

is a [pullback](foundation-core.pullbacks.md) if each summand is.

## Definitions

### Coproduct cones

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  coproduct-cone :
    cone f g C → cone f' g' C' →
    cone (map-coproduct f f') (map-coproduct g g') (C + C')
  pr1 (coproduct-cone (p , q , H) (p' , q' , H')) = map-coproduct p p'
  pr1 (pr2 (coproduct-cone (p , q , H) (p' , q' , H'))) = map-coproduct q q'
  pr2 (pr2 (coproduct-cone (p , q , H) (p' , q' , H'))) =
    ( inv-htpy (preserves-comp-map-coproduct p f p' f')) ∙h
    ( htpy-map-coproduct H H') ∙h
    ( preserves-comp-map-coproduct q g q' g')
```

## Properties

### Computing the standard pullback of a coproduct

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  inl-map-standard-pullback-coproduct :
    standard-pullback f g →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  pr1 (inl-map-standard-pullback-coproduct (x , y , p)) = inl x
  pr1 (pr2 (inl-map-standard-pullback-coproduct (x , y , p))) = inl y
  pr2 (pr2 (inl-map-standard-pullback-coproduct (x , y , p))) = ap inl p

  inr-map-standard-pullback-coproduct :
    standard-pullback f' g' →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  pr1 (inr-map-standard-pullback-coproduct (x , y , p)) = inr x
  pr1 (pr2 (inr-map-standard-pullback-coproduct (x , y , p))) = inr y
  pr2 (pr2 (inr-map-standard-pullback-coproduct (x , y , p))) = ap inr p

  map-standard-pullback-coproduct :
    standard-pullback f g + standard-pullback f' g' →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  map-standard-pullback-coproduct (inl v) =
    inl-map-standard-pullback-coproduct v
  map-standard-pullback-coproduct (inr u) =
    inr-map-standard-pullback-coproduct u

  map-inv-standard-pullback-coproduct :
    standard-pullback (map-coproduct f f') (map-coproduct g g') →
    standard-pullback f g + standard-pullback f' g'
  map-inv-standard-pullback-coproduct (inl x , inl y , p) =
    inl (x , y , is-injective-inl p)
  map-inv-standard-pullback-coproduct (inr x , inr y , p) =
    inr (x , y , is-injective-inr p)

  is-section-map-inv-standard-pullback-coproduct :
    is-section
      ( map-standard-pullback-coproduct)
      ( map-inv-standard-pullback-coproduct)
  is-section-map-inv-standard-pullback-coproduct (inl x , inl y , p) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (is-section-is-injective-inl p))
  is-section-map-inv-standard-pullback-coproduct (inr x , inr y , p) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (is-section-is-injective-inr p))

  is-retraction-map-inv-standard-pullback-coproduct :
    is-retraction
      ( map-standard-pullback-coproduct)
      ( map-inv-standard-pullback-coproduct)
  is-retraction-map-inv-standard-pullback-coproduct (inl (x , y , p)) =
    ap
      ( inl)
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (is-retraction-is-injective-inl p)))
  is-retraction-map-inv-standard-pullback-coproduct (inr (x , y , p)) =
    ap
      ( inr)
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (is-retraction-is-injective-inr p)))

  abstract
    is-equiv-map-standard-pullback-coproduct :
      is-equiv map-standard-pullback-coproduct
    is-equiv-map-standard-pullback-coproduct =
      is-equiv-is-invertible
        map-inv-standard-pullback-coproduct
        is-section-map-inv-standard-pullback-coproduct
        is-retraction-map-inv-standard-pullback-coproduct

  compute-standard-pullback-coproduct :
    standard-pullback f g + standard-pullback f' g' ≃
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  compute-standard-pullback-coproduct =
    map-standard-pullback-coproduct , is-equiv-map-standard-pullback-coproduct
```

### The gap map of a coproduct computes as a coproduct of gap maps

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  triangle-map-standard-pullback-coproduct :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'}
    (c : cone f g C) (c' : cone f' g' C') →
    coherence-triangle-maps
      ( gap
        ( map-coproduct f f')
        ( map-coproduct g g')
        ( coproduct-cone f g f' g' c c'))
      ( map-standard-pullback-coproduct f g f' g')
      ( map-coproduct (gap f g c) (gap f' g' c'))
  triangle-map-standard-pullback-coproduct c c' (inl _) =
    eq-pair-eq-fiber (eq-pair-eq-fiber right-unit)
  triangle-map-standard-pullback-coproduct c c' (inr _) =
    eq-pair-eq-fiber (eq-pair-eq-fiber right-unit)
```

### Coproducts of pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  abstract
    is-pullback-coproduct-is-pullback :
      (c : cone f g C) (c' : cone f' g' C') →
      is-pullback f g c →
      is-pullback f' g' c' →
      is-pullback
        ( map-coproduct f f')
        ( map-coproduct g g')
        ( coproduct-cone f g f' g' c c')
    is-pullback-coproduct-is-pullback c c' is-pb-c is-pb-c' =
      is-equiv-left-map-triangle
        ( gap
          ( map-coproduct f f')
          ( map-coproduct g g')
          ( coproduct-cone f g f' g' c c'))
        ( map-standard-pullback-coproduct f g f' g')
        ( map-coproduct (gap f g c) (gap f' g' c'))
        ( triangle-map-standard-pullback-coproduct f g f' g' c c')
        ( is-equiv-map-coproduct is-pb-c is-pb-c')
        ( is-equiv-map-standard-pullback-coproduct f g f' g')
```

### Coproducts of cones that satisfy the universal property of pullbacks satisfy the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  abstract
    universal-property-pullback-coproduct-universal-property-pullback :
      (c : cone f g C) (c' : cone f' g' C') →
      universal-property-pullback f g c →
      universal-property-pullback f' g' c' →
      universal-property-pullback
        ( map-coproduct f f')
        ( map-coproduct g g')
        ( coproduct-cone f g f' g' c c')
    universal-property-pullback-coproduct-universal-property-pullback
      c c' up-pb-c up-pb-c' =
      universal-property-pullback-is-pullback
        ( map-coproduct f f')
        ( map-coproduct g g')
        ( coproduct-cone f g f' g' c c')
        ( is-pullback-coproduct-is-pullback f g f' g' c c'
          ( is-pullback-universal-property-pullback f g c up-pb-c)
          ( is-pullback-universal-property-pullback f' g' c' up-pb-c'))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
