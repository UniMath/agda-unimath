# Lower retracts of strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.lower-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.rounded-lower-subsets-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.lower-types-preorders
open import order-theory.order-preserving-maps-preorders
open import order-theory.strict-order-preserving-maps
open import order-theory.strict-subpreorders
open import order-theory.subpreorders

open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

A
[strictly increasing map](real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f : [a, b] → ℝ` on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
has a
{{#concept "lower retract" Disambiguation"of a strictly increasing real map on a proper closed interval Agda=lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ}}
defined in the
[lower dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md)
defined as follows:

For any `y ∈ [f(a), f(b)]` and `r : ℚ`,

```text
  r < lower-f⁻¹ y ⇔ ∃ (q : ℚ) | (r < q) ∧ (q < b) ∧ (f q ≤ y),
```

i.e., `r` is lesser than the lower inverse iff there exists a rational interior
point `q ∈ [r, b]` with image lesser than or equal to `y`.

Informally, `lower-f⁻¹ y` is the largest lower real whose image by `f`
approaches `y` **below** it.

## Definitions

### The lower preimage of a strictly increasing map on a proper closed interval

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where

  subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l4) ℚ
  subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
    q =
    ( lower-cut-ℝ (upper-bound-proper-closed-interval-ℝ I) q) ∧
    ( leq-prop-ℝ
      ( clamp-real-map-proper-closed-interval-ℝ I
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( raise-real-ℚ l1 q))
      ( v))

  abstract
    is-lower-subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-downwards-closed-subtype-Preorder
        ( ℚ-Preorder)
        ( subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ)
    is-lower-subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
      q r r≤q (Lq , Hq) =
      ( ( leq-lower-cut-ℝ
          ( upper-bound-proper-closed-interval-ℝ I)
          ( r≤q)
          ( Lq)) ,
        transitive-leq-ℝ
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l1 r))
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l1 q))
          ( v)
          ( Hq)
          ( leq-map-clamp-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( _)
            ( _)
            ( leq-raise-leq-ℝ l1 (preserves-leq-real-ℚ r≤q))))

  lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
    lower-type-Preorder (l2 ⊔ l4) ℚ-Preorder
  lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ =
    ( subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ ,
      is-lower-subtype-lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

### The lower retract of a strictly increasing map on a proper closed interval

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where

  lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l4) ℚ
  lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ =
    subtype-round-lower-type-ℚ
      ( lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))

  is-in-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℚ → UU (l2 ⊔ l4)
  is-in-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    type-Prop ∘
    lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ

  abstract opaque
    unfolding le-ℝ

    is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (r : ℚ) →
      le-ℝ (real-ℚ r) (lower-bound-proper-closed-interval-ℝ I) →
      is-in-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r)
    is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
      r r<a =
      let
        open
          do-syntax-trunc-Prop
            ( lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r))
      in do
        ( q , r<q , q<a) ← r<a
        let
          lemma-r<q : le-ℚ r q
          lemma-r<q =
            reflects-le-real-ℚ
                ( le-real-is-in-upper-cut-ℝ (real-ℚ r) r<q)

          lemma-q≤a :
            leq-ℝ
              ( raise-real-ℚ l1 q)
              ( lower-bound-proper-closed-interval-ℝ I)
          lemma-q≤a =
            leq-le-ℝ
              ( le-raise-real-is-in-lower-cut-ℝ
                ( l1)
                ( lower-bound-proper-closed-interval-ℝ I)
                ( q<a))

          lemma-leq-clamp-fq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
              ( lower-bound-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
          lemma-leq-clamp-fq =
            is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( I)
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( _)
              ( _)
              ( preserves-leq-right-sim-ℝ
                ( sim-raise-in-proper-closed-interval-lower-bound-proper-closed-interval-ℝ
                  ( I)
                  ( l1))
                ( leq-sim-ℝ
                  ( sim-clamp-leq-lower-bound-closed-interval-ℝ
                    ( closed-interval-proper-closed-interval-ℝ I)
                    ( raise-real-ℚ l1 q)
                    ( lemma-q≤a))))

          lemma-leq :
            leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
              ( v)
          lemma-leq =
            transitive-leq-ℝ
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
              ( lower-bound-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
              ( v)
              ( lo-bound)
              ( lemma-leq-clamp-fq)

          lemma-le :
            is-in-lower-cut-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( q)
          lemma-le =
            is-in-lower-cut-le-real-ℚ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( transitive-le-ℝ
                ( real-ℚ q)
                ( lower-bound-proper-closed-interval-ℝ I)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( le-bounds-proper-closed-interval-ℝ I)
                ( le-real-is-in-lower-cut-ℝ
                  ( lower-bound-proper-closed-interval-ℝ I)
                  ( q<a)))

        intro-exists q (lemma-r<q , lemma-le , lemma-leq)

  abstract
    is-inhabited-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-inhabited-subtype
        lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-inhabited-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ))
      in do
        ( r , r<a) ←
          exists-lesser-rational-ℝ (lower-bound-proper-closed-interval-ℝ I)

        intro-exists r
          ( is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( r)
            ( r<a))

  lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    lower-ℝ (l2 ⊔ l4)
  lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ =
    lower-real-is-inhabited-rounded-lower-type-ℚ
      ( round-lower-type-ℚ
        ( lower-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( y)))
      ( is-inhabited-lower-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

## Properties

### The image of a rational in the lower cut of the lower inverse at a point is lesser than or equal to it

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where abstract

  leq-map-is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ :
    (r : ℚ) →
    is-in-cut-lower-ℝ
      ( lower-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
      ( r) →
    leq-ℝ
      ( clamp-real-map-proper-closed-interval-ℝ I
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( raise-real-ℚ l1 r))
      ( v)
  leq-map-is-in-lower-cut-map-inv-le-lower-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
    r lo =
    let
      open
        do-syntax-trunc-Prop
          ( leq-prop-ℝ
            ( clamp-real-map-proper-closed-interval-ℝ I
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( raise-real-ℚ l1 r))
            ( v))
    in do
      (q , r<q , q<b , Hq) ← lo

      transitive-leq-ℝ
        ( clamp-real-map-proper-closed-interval-ℝ I
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( raise-real-ℚ l1 r))
        ( clamp-real-map-proper-closed-interval-ℝ I
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( raise-real-ℚ l1 q))
        ( v)
        ( Hq)
        ( is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( I)
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( _)
          ( _)
          ( is-increasing-map-clamp-closed-interval-ℝ
            ( closed-interval-proper-closed-interval-ℝ I)
            ( _)
            ( _)
            ( leq-raise-leq-ℝ l1 (leq-le-ℝ (preserves-le-real-ℚ r<q)))))
```
