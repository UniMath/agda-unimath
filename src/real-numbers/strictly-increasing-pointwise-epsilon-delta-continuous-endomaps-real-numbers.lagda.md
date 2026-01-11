# Strictly increasing pointwise ε-δ continuous endomaps on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
```

</details>

## Idea

This page describes the interaction of
[pointwise ε-δ continuity of endomaps of real numbers](real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers.md)
and being
[strictly increasing](real-numbers.strictly-increasing-endomaps-real-numbers.md).

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  is-strictly-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ :
    Prop (lsuc l1 ⊔ l2)
  is-strictly-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ =
    is-strictly-increasing-prop-endomap-ℝ
      ( map-pointwise-ε-δ-continuous-endomap-ℝ f)

  is-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    type-Prop is-strictly-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ

strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2 =
  type-subtype
    ( is-strictly-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  pointwise-ε-δ-continuous-endomap-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    pointwise-ε-δ-continuous-endomap-ℝ l1 l2
  pointwise-ε-δ-continuous-endomap-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr1 f

  map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ : ℝ l1 → ℝ l2
  map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    map-pointwise-ε-δ-continuous-endomap-ℝ
      ( pointwise-ε-δ-continuous-endomap-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-strictly-increasing-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-strictly-increasing-endomap-ℝ
      ( map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-strictly-increasing-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr2 f

  is-pointwise-ε-δ-continuous-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-pointwise-ε-δ-continuous-endomap-ℝ
      ( map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-pointwise-ε-δ-continuous-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
      ( pointwise-ε-δ-continuous-endomap-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

## Properties

### If a classically pointwise continuous function is strictly increasing on a dense subset of ℝ, then it is strictly increasing on ℝ

```agda
module _
  {l1 l2 l3 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  (S : dense-subset-ℝ l3 l1)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ :
      is-strictly-increasing-on-subset-endomap-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
        ( subset-dense-subset-ℝ S) →
      is-strictly-increasing-endomap-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
    is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ
      H x y x<y =
      let
        H' =
          is-increasing-is-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( S)
            ( is-increasing-is-increasing-on-strict-inequalities-on-subset-endomap-ℝ
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
              ( subset-dense-subset-ℝ S)
              ( λ a b a<b → leq-le-ℝ (H a b a<b)))
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f x)
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f y))
      in do
        (a , a∈S , x<a , a<y) ← dense-le-dense-subset-ℝ S x<y
        (b , b∈S , a<b , b<y) ← dense-le-dense-subset-ℝ S a<y
        concatenate-leq-le-ℝ
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f x)
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f a)
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f y)
          ( H' x a (leq-le-ℝ x<a))
          ( concatenate-le-leq-ℝ
            ( map-pointwise-ε-δ-continuous-endomap-ℝ f a)
            ( map-pointwise-ε-δ-continuous-endomap-ℝ f b)
            ( map-pointwise-ε-δ-continuous-endomap-ℝ f y)
            ( H (a , a∈S) (b , b∈S) a<b)
            ( H' b y (leq-le-ℝ b<y)))
```

### If `f` is classically pointwise continuous and strictly increasing on the rational real numbers, it is strictly increasing on the real numbers

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-rational-pointwise-ε-δ-continuous-endomap-ℝ :
      ( (p q : ℚ) → le-ℚ p q →
        le-ℝ
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f (raise-real-ℚ l1 p))
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f (raise-real-ℚ l1 q))) →
      is-strictly-increasing-endomap-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
    is-strictly-increasing-is-strictly-increasing-rational-pointwise-ε-δ-continuous-endomap-ℝ H =
      is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( dense-subset-rational-ℝ l1)
        ( λ (x , p , x~p) (y , q , y~q) x<y →
          binary-tr
            ( le-ℝ)
            ( ap
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
              ( inv (eq-raise-real-rational-is-rational-ℝ x~p)))
            ( ap
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
              ( inv (eq-raise-real-rational-is-rational-ℝ y~q)))
            ( H
              ( p)
              ( q)
              ( reflects-le-real-ℚ
                ( le-le-raise-ℝ l1
                  ( binary-tr
                    ( le-ℝ)
                    ( eq-raise-real-rational-is-rational-ℝ x~p)
                    ( eq-raise-real-rational-is-rational-ℝ y~q)
                    ( x<y))))))
```

### Strictly increasing, pointwise ε-δ continuous maps reflect strict inequality

```agda
module _
  {l1 l2 : Level}
  (f : strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  abstract
    reflects-le-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (x y : ℝ l1) →
      le-ℝ
        ( map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ f x)
        ( map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ f y) →
      le-ℝ x y
    reflects-le-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      x y fx<fy =
      let
        map-f = map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ f
        open do-syntax-trunc-Prop (le-prop-ℝ x y)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (ε , fx+ε<y) ← exists-positive-rational-separation-le-ℝ fx<fy
        (δ , Hδ) ←
          is-pointwise-ε-δ-continuous-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( x)
            ( ε)
        concatenate-le-leq-ℝ
          ( x)
          ( x +ℝ real-ℚ⁺ δ)
          ( y)
          ( le-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ δ))
          ( reflects-leq-is-strictly-increasing-endomap-ℝ
            ( map-f)
            ( is-strictly-increasing-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f))
            ( x +ℝ real-ℚ⁺ δ)
            ( y)
            ( chain-of-inequalities
              map-f (x +ℝ real-ℚ⁺ δ)
              ≤ map-f x +ℝ real-ℚ⁺ ε
                by
                  right-leq-real-bound-neighborhood-ℝ
                    ( ε)
                    ( map-f x)
                    ( map-f (x +ℝ real-ℚ⁺ δ))
                    ( Hδ (x +ℝ real-ℚ⁺ δ) (neighborhood-right-add-real-ℚ⁺ x δ))
              ≤ map-f y by leq-le-ℝ fx+ε<y))
```
