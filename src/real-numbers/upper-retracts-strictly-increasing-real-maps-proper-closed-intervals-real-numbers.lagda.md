# Upper retracts of strictly increasing real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.upper-retracts-strictly-increasing-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.rounded-upper-subsets-rational-numbers
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

open import order-theory.strict-order-preserving-maps
open import order-theory.strict-subpreorders
open import order-theory.subpreorders
open import order-theory.upper-types-preorders

open import real-numbers.clamp-function-closed-interval-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maps-between-proper-closed-intervals-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-maps-proper-closed-intervals-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A
[strictly increasing map](real-numbers.strictly-increasing-real-maps-proper-closed-intervals-real-numbers.md)
`f : [a, b] → ℝ` on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
has an
{{#concept "upper retract" Disambiguation"of a strictly increasing real map on a proper closed interval Agda=upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ}}
defined in the
[upper dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md)
defined as follows:

For any `y ∈ [f(a), f(b)]` and `r : ℚ`,

```text
  upper-f⁻¹ y < r ⇔ ∃ (q : ℚ) | (q < r) ∧ (a < q) ∧ (y ≤ f q)
```

i.e., `r` is greater than the upper inverse iff there exists a rational interior
point `q ∈ [a, r]` with image lesser than or equal to `y`.

Informally, `upper-f⁻¹ y` is the smallest upper real whose image by `f`
approaches `y` **above** it.

## Definitions

### The upper preimage of a strictly increasing map on a proper closed interval

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where

  subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l3) ℚ
  subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
    q =
    ( upper-cut-ℝ (lower-bound-proper-closed-interval-ℝ I) q) ∧
    ( leq-prop-ℝ
      ( v)
      ( clamp-real-map-proper-closed-interval-ℝ I
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( raise-real-ℚ l1 q)))

  abstract
    is-upper-subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-upwards-closed-subtype-Preorder
        ( ℚ-Preorder)
        ( subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ)
    is-upper-subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
      r q r≤q (Lr , Hr) =
      ( ( leq-upper-cut-ℝ
          ( lower-bound-proper-closed-interval-ℝ I)
          ( r≤q)
          ( Lr)) ,
        ( transitive-leq-ℝ
          ( v)
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l1 r))
          ( clamp-real-map-proper-closed-interval-ℝ I
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( raise-real-ℚ l1 q))
          ( leq-map-clamp-is-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( I)
            ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
            ( _)
            ( _)
            ( leq-raise-leq-ℝ l1 (preserves-leq-real-ℚ r≤q)))
          ( Hr)))

  upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ :
    upper-type-Preorder (l2 ⊔ l3) ℚ-Preorder
  upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ =
    ( subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ ,
      is-upper-subtype-upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

### The upper inverse of a strictly increasing map on a proper closed interval

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where

  upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    subtype (l2 ⊔ l3) ℚ
  upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ =
    subtype-round-upper-type-ℚ
      ( upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))

  is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ℚ → UU (l2 ⊔ l3)
  is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    =
    type-Prop ∘
    upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ

  abstract opaque
    unfolding le-ℝ

    is-in-upper-cut-map-inv-le-upper-bound-strictly-increasing-real-map-proper-closed-interval-ℝ :
      (r : ℚ) →
      le-ℝ (upper-bound-proper-closed-interval-ℝ I) (real-ℚ r) →
      is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( r)
    is-in-upper-cut-map-inv-le-upper-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
      r b<r =
      let
        open
          do-syntax-trunc-Prop
            ( upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( r))
      in do
        ( q , b<q , q<r) ← b<r

        let
          lemma-q<r : le-ℚ q r
          lemma-q<r =
            reflects-le-real-ℚ
                ( le-real-is-in-lower-cut-ℝ (real-ℚ r) q<r)

          lemma-b≤q :
            leq-ℝ
              ( upper-bound-proper-closed-interval-ℝ I)
              ( raise-real-ℚ l1 q)
          lemma-b≤q =
            leq-le-ℝ
              ( le-raise-real-is-in-upper-cut-ℝ
                ( l1)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( b<q))

          lemma-leq-clamp-fq :
            leq-ℝ
              ( upper-bound-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
          lemma-leq-clamp-fq =
            is-increasing-is-strictly-increasing-real-map-proper-closed-interval-ℝ
              ( I)
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( le-map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( _)
              ( _)
              ( preserves-leq-left-sim-ℝ
                ( sim-raise-in-proper-closed-interval-upper-bound-proper-closed-interval-ℝ
                  ( I)
                  ( l1))
                ( leq-sim-ℝ
                  ( symmetric-sim-ℝ
                    ( sim-clamp-leq-upper-bound-closed-interval-ℝ
                      ( closed-interval-proper-closed-interval-ℝ I)
                      ( raise-real-ℚ l1 q)
                      ( lemma-b≤q)))))
          lemma-leq :
            leq-ℝ
              ( v)
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
          lemma-leq =
            transitive-leq-ℝ
              ( v)
              ( upper-bound-proper-closed-interval-ℝ
                ( im-strictly-increasing-real-map-proper-closed-interval-ℝ f))
              ( clamp-real-map-proper-closed-interval-ℝ I
                ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
                ( raise-real-ℚ l1 q))
              ( lemma-leq-clamp-fq)
              ( hi-bound)

          lemma-le :
            is-in-upper-cut-ℝ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( q)
          lemma-le =
            is-in-upper-cut-le-real-ℚ
              ( lower-bound-proper-closed-interval-ℝ I)
              ( transitive-le-ℝ
                ( lower-bound-proper-closed-interval-ℝ I)
                ( upper-bound-proper-closed-interval-ℝ I)
                ( real-ℚ q)
                ( le-real-is-in-upper-cut-ℝ
                  ( upper-bound-proper-closed-interval-ℝ I)
                  ( b<q))
                ( le-bounds-proper-closed-interval-ℝ I))

        intro-exists q (lemma-q<r , lemma-le , lemma-leq)

  abstract
    is-inhabited-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
      is-inhabited-subtype
        upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    is-inhabited-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
      =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ))
      in do
        ( r , b<r) ←
          exists-greater-rational-ℝ (upper-bound-proper-closed-interval-ℝ I)

        intro-exists r
          ( is-in-upper-cut-map-inv-le-upper-bound-strictly-increasing-real-map-proper-closed-interval-ℝ
            ( r)
            ( b<r))

  upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    upper-ℝ (l2 ⊔ l3)
  upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ =
    upper-real-is-inhabited-rounded-upper-type-ℚ
      ( round-upper-type-ℚ
        ( upper-preimage-strictly-increasing-real-map-proper-closed-interval-ℝ
          ( f)
          ( y)))
      ( is-inhabited-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ)
```

## Properties

### The image of a rational in the upper cut of the inverse at a point is greater than or equal to it

```agda
module _
  { l1 l2 l3 l4 : Level}
  { I : proper-closed-interval-ℝ l3 l4}
  ( f :
    strictly-increasing-real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 I)
  ( y@(v , lo-bound , hi-bound) :
    type-im-strictly-increasing-real-map-proper-closed-interval-ℝ l2 f)
  where abstract

  leq-map-is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ :
    ( r : ℚ) →
    ( is-in-cut-upper-ℝ
      ( upper-real-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
        ( f)
        ( y))
      ( r)) →
    leq-ℝ
      ( v)
      ( clamp-real-map-proper-closed-interval-ℝ I
        ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
        ( raise-real-ℚ l1 r))
  leq-map-is-in-upper-cut-map-inv-strictly-increasing-real-map-proper-closed-interval-ℝ
    r hi =
    let
      open
        do-syntax-trunc-Prop
          ( leq-prop-ℝ
            ( v)
            ( clamp-real-map-proper-closed-interval-ℝ I
              ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
              ( raise-real-ℚ l1 r)))
    in do
      ( q , q<r , a<q , Hq) ← hi

      transitive-leq-ℝ
        ( v)
        ( clamp-real-map-proper-closed-interval-ℝ I
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( raise-real-ℚ l1 q))
        ( clamp-real-map-proper-closed-interval-ℝ I
          ( map-strictly-increasing-real-map-proper-closed-interval-ℝ f)
          ( raise-real-ℚ l1 r))
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
            ( leq-raise-leq-ℝ l1 (leq-le-ℝ (preserves-le-real-ℚ q<r)))))
        ( Hq)
```
