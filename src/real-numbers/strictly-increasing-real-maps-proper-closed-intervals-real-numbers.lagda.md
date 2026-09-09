# Strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.strict-order-preserving-maps
open import order-theory.strict-subpreorders
open import order-theory.subpreorders

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real map](real-numbers.real-maps-proper-closed-intervals-real-numbers.md) `f`
on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]` is
{{#concept "strictly increasing" Disambiguation="real map on proper closerd interval of real numbers" Agda=is-strictly-increasing-real-map-proper-closed-interval-ℝ}}
if, for any `x , y ∈ [a, b]`, if `x < y`, then `f x < f y`.

## Definitions

### The property of being a strictly increasing real map on a proper closed interval

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  where

  is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ :
    real-map-proper-closed-interval-ℝ l1 l2 I →
    Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ =
    preserves-strict-order-prop-map-Strict-Preorder
      ( strict-preorder-Strict-Subpreorder
        ( strict-preorder-ℝ l1)
        ( subtype-proper-closed-interval-ℝ l1 I))
      ( strict-preorder-ℝ l2)

  is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    real-map-proper-closed-interval-ℝ l1 l2 I →
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    type-Prop ∘ is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ

  is-prop-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (f : real-map-proper-closed-interval-ℝ l1 l2 I) →
    is-prop (is-strictly-increasing-real-map-proper-closed-interval-ℝ f)
  is-prop-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    is-prop-type-Prop ∘
    is-strictly-increasing-prop-real-map-proper-closed-interval-ℝ
```

## Properties

### A strictly increasing map on a proper closed interval is increasing

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  where abstract

  is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-strictly-increasing-real-map-proper-closed-interval-ℝ I f →
    preserves-order-Preorder
      ( preorder-Subpreorder
        ( ℝ-Preorder l1)
        ( subtype-proper-closed-interval-ℝ l1 I))
      ( ℝ-Preorder l2)
      ( f)
  is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    H x@(u , _) y@(v , _) u≤v =
    double-negation-elim-leq-ℝ
      ( f x)
      ( f y)
      ( map-double-negation
        ( rec-coproduct
          ( λ u~v →
            leq-eq-ℝ
              ( ap f
                ( eq-type-subtype
                  ( subtype-proper-closed-interval-ℝ l1 I)
                  ( eq-sim-ℝ u~v))))
          ( λ u<v → leq-le-ℝ (H x y u<v)))
        ( irrefutable-sim-or-le-leq-ℝ u v u≤v))
```

### Strictly increasing maps on proper closed intervals reflect inequality

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( x@(u , _) y@(v , _) : type-proper-closed-interval-ℝ l1 I) →
    leq-ℝ (f x) (f y) →
    leq-ℝ u v
  reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , _) y@(v , _) K =
    leq-not-le-ℝ v u (not-le-leq-ℝ (f x) (f y) K ∘ (H y x))
```

### Strictly increasing maps on proper closed intervals are embeddings

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ l1 l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    is-injective f
  is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    {x@(u , _)} {y@(v , _)} fx=fy =
    eq-type-subtype
      ( subtype-proper-closed-interval-ℝ l1 I)
      ( antisymmetric-leq-ℝ u v
        ( reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( x)
          ( y)
          ( leq-eq-ℝ fx=fy))
        ( reflects-leq-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( f)
          ( H)
          ( y)
          ( x)
          ( leq-eq-ℝ (inv fx=fy))))

  is-emb-is-strictly-increasing-real-map-proper-closed-interval-ℝ : is-emb f
  is-emb-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    is-emb-is-injective
      ( is-set-ℝ l2)
      ( is-injective-is-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

### The images of the bounds of a proper closed interval by a strictly increasing map are strictly ordered

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    le-ℝ
      ( f
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1)))
      ( f
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1)))
  le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ =
    H
      ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
        ( I)
        ( l1))
      ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
        ( I)
        ( l1))
      ( preserves-le-sim-ℝ
        ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( le-bounds-proper-closed-interval-ℝ I))

  proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    proper-closed-interval-ℝ l2 l2
  proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    ( ( f
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))) ,
      ( f
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))) ,
      ( le-im-bounds-is-strictly-increasing-real-map-proper-closed-interval-ℝ))
```

### The image of a strictly increasing map on a proper closed interval is contained in the interval image of its bounds

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where abstract

  is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (x : type-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) I) →
    is-in-proper-closed-interval-ℝ
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
      ( f x)
  is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x@(u , lo-bound , hi-bound) =
    ( ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( x)
        ( preserves-leq-left-sim-ℝ
          ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( lo-bound))) ,
      ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x)
        ( raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
          ( I)
          ( l1))
        ( preserves-leq-right-sim-ℝ
          ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
            ( I)
            ( l1))
          ( hi-bound))))
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (I : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  (H : is-strictly-increasing-real-map-proper-closed-interval-ℝ I f)
  where

  map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ :
    map-proper-closed-interval-ℝ _ _
      ( I)
      ( proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H))
  map-proper-closed-interval-is-strictly-increasing-real-map-proper-closed-interval-ℝ
    x =
    ( f x ,
      is-in-proper-closed-interval-im-is-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( I)
        ( f)
        ( H)
        ( x))
```
