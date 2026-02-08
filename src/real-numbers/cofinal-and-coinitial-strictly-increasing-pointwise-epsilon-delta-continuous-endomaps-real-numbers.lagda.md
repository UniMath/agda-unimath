# Cofinal and coinitial, strictly increasing, pointwise ε-δ continuous endomaps on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cofinal-and-coinitial-strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.automorphisms
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-space-of-rational-numbers

open import order-theory.large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cofinal-and-coinitial-endomaps-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
open import real-numbers.strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
```

</details>

## Idea

If an [endomap](foundation.endomorphisms.md) on the
[real numbers](real-numbers.dedekind-real-numbers.md) is

- [cofinal and coinitial](real-numbers.cofinal-and-coinitial-endomaps-real-numbers.md)
- [strictly increasing](real-numbers.strictly-increasing-endomaps-real-numbers.md)
- [pointwise ε-δ continuous](real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers.md)

then it is an [automorphism](foundation.automorphisms.md) of the real numbers,
and its inverse also has those properties.

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  is-cofinal-and-coinitial-prop-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    Prop (lsuc l1 ⊔ l2)
  is-cofinal-and-coinitial-prop-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-cofinal-and-coinitial-prop-endomap-ℝ
      ( map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ f)

  is-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    UU (lsuc l1 ⊔ l2)
  is-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    type-Prop
      ( is-cofinal-and-coinitial-prop-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
  l1 l2 =
  type-subtype
    ( is-cofinal-and-coinitial-prop-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      { l1}
      { l2})

module _
  {l1 l2 : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l1)
      ( l2))
  where

  strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2
  strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr1 f

  map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    ℝ l1 → ℝ l2
  map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-cofinal-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-cofinal-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-cofinal-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr1 (pr2 f)

  is-coinitial-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-coinitial-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-coinitial-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr2 (pr2 f)

  is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-strictly-increasing-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-strictly-increasing-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-increasing-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-increasing-is-strictly-increasing-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
      ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-pointwise-ε-δ-continuous-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-pointwise-ε-δ-continuous-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-pointwise-ε-δ-continuous-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-pointwise-ε-δ-continuous-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-injective-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-injective
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-injective-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-injective-is-strictly-increasing-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
      ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  reflects-le-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    (x x' : ℝ l1) →
    le-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( x))
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( x')) →
    le-ℝ x x'
  reflects-le-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    reflects-le-map-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( strictly-increasing-pointwise-ε-δ-continuous-endomap-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    (x x' : ℝ l1) →
    leq-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( x))
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( x')) →
    leq-ℝ x x'
  reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    reflects-leq-is-strictly-increasing-endomap-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
      ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

## Properties

### The inverse map of an cofinal and coinitial, strictly increasing, pointwise ε-δ continuous map

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  (y : ℝ l)
  where

  lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    subtype l ℚ
  lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
    q =
    le-prop-ℝ
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( raise-real-ℚ l q))
      ( y)

  is-in-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    ℚ → UU l
  is-in-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-in-subtype
      ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    subtype l ℚ
  upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
    q =
    le-prop-ℝ
      ( y)
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( raise-real-ℚ l q))

  is-in-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    ℚ → UU l
  is-in-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-in-subtype
      ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  abstract
    is-inhabited-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-inhabited-subtype
        ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
    is-inhabited-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ))
      in do
        (q , q<y) ← exists-lesser-rational-ℝ y
        (x , fx≤q) ←
          is-coinitial-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( q)
        (p , p<x) ← exists-lesser-rational-ℝ x
        intro-exists
          ( p)
          ( transitive-le-ℝ
            ( map-f (raise-real-ℚ l p))
            ( map-f x)
            ( y)
            ( concatenate-leq-le-ℝ (map-f x) (real-ℚ q) y fx≤q q<y)
            ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( raise-real-ℚ l p)
              ( x)
              ( preserves-le-left-raise-ℝ l p<x)))

    is-inhabited-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-inhabited-subtype
        ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
    is-inhabited-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop
              ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ))
      in do
        (q , y<q) ← exists-greater-rational-ℝ y
        (x , q≤fx) ←
          is-cofinal-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( q)
        (p , x<p) ← exists-greater-rational-ℝ x
        intro-exists
          ( p)
          ( transitive-le-ℝ
            ( y)
            ( map-f x)
            ( map-f (raise-real-ℚ l p))
            ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( x)
              ( raise-real-ℚ l p)
              ( preserves-le-right-raise-ℝ l x<p))
            ( concatenate-le-leq-ℝ y (real-ℚ q) (map-f x) y<q q≤fx))

    forward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      is-in-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q) →
      exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop q r) ∧
          ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r)))
    forward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q fq<y =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ)
              ( λ r →
                ( le-ℚ-Prop q r) ∧
                ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                  ( r))))
      in do
        (ε , fq+ε<y) ← exists-positive-rational-separation-le-ℝ fq<y
        (δ , H) ←
          is-pointwise-ε-δ-continuous-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( raise-real-ℚ l q)
            ( ε)
        intro-exists
          ( q +ℚ rational-ℚ⁺ δ)
          ( le-right-add-rational-ℚ⁺ q δ ,
            concatenate-leq-le-ℝ
              ( map-f (raise-real-ℚ l (q +ℚ rational-ℚ⁺ δ)))
              ( map-f (raise-real-ℚ l q) +ℝ real-ℚ⁺ ε)
              ( y)
              ( left-leq-real-bound-neighborhood-ℝ
                ( ε)
                ( _)
                ( _)
                ( is-symmetric-neighborhood-ℝ _ _ _
                  ( H
                    ( raise-real-ℚ l (q +ℚ rational-ℚ⁺ δ))
                    ( forward-implication
                      ( is-isometry-raise-real-ℚ l δ _ _)
                      ( neighborhood-right-add-rational-ℚ⁺ q δ)))))
              ( fq+ε<y))

    forward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      is-in-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q) →
      exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop r q) ∧
          ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r)))
    forward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q y<fq =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ)
              ( λ r →
                ( le-ℚ-Prop r q) ∧
                ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                  ( r))))
      in do
        (ε , y+ε<fq) ← exists-positive-rational-separation-le-ℝ y<fq
        (δ , H) ←
          is-pointwise-ε-δ-continuous-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( raise-real-ℚ l q)
            ( ε)
        intro-exists
          ( q -ℚ rational-ℚ⁺ δ)
          ( le-diff-rational-ℚ⁺ q δ ,
            concatenate-le-leq-ℝ
              ( y)
              ( map-f (raise-real-ℚ l q) -ℝ real-ℚ⁺ ε)
              ( map-f (raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ)))
              ( le-transpose-left-add-ℝ _ _ _ y+ε<fq)
              ( leq-transpose-right-add-ℝ _ _ _
                ( left-leq-real-bound-neighborhood-ℝ _ _ _
                  ( H
                    ( raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ))
                    ( forward-implication
                      ( is-isometry-raise-real-ℚ l δ _ _)
                      ( neighborhood-right-diff-rational-ℚ⁺ q δ))))))

    backward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop q r) ∧
          ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r))) →
      is-in-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q)
    backward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      elim-exists
        ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q))
        ( λ r (q<r , fr<y) →
          transitive-le-ℝ _ _ _
            ( fr<y)
            ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( raise-real-ℚ l q)
              ( raise-real-ℚ l r)
              ( le-raise-le-ℝ l (preserves-le-real-ℚ q<r))))

    backward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop r q) ∧
          ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r))) →
      is-in-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q)
    backward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      elim-exists
        ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q))
        ( λ r (r<q , y<fr) →
          transitive-le-ℝ _ _ _
            ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( raise-real-ℚ l r)
              ( raise-real-ℚ l q)
              ( le-raise-le-ℝ l (preserves-le-real-ℚ r<q)))
            ( y<fr))

    is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      ( is-in-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q)) ↔
      ( exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop q r) ∧
          ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r))))
    is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      ( forward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q) ,
        backward-implication-is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q))

    is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (q : ℚ) →
      ( is-in-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( q)) ↔
      ( exists
        ( ℚ)
        ( λ r →
          ( le-ℚ-Prop r q) ∧
          ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( r))))
    is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      ( forward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q) ,
        backward-implication-is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q))

    is-disjoint-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      disjoint-subtype
        ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
        ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
    is-disjoint-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q (fq<y , y<fq) =
      asymmetric-le-ℝ fq<y y<fq

    is-located-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( p))
        ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( q))
    is-located-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      p q p<q =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
      in
        cotransitive-le-ℝ
          ( map-f (raise-real-ℚ l p))
          ( map-f (raise-real-ℚ l q))
          ( y)
          ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( raise-real-ℚ l p)
            ( raise-real-ℚ l q)
            ( le-raise-le-ℝ l (preserves-le-real-ℚ p<q)))

  opaque
    map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      ℝ l
    map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      ( ( lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ ,
          is-inhabited-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ ,
          is-rounded-lower-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ) ,
        ( upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ ,
          is-inhabited-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ ,
          is-rounded-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ) ,
        is-disjoint-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ ,
        is-located-lower-upper-cut-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

### The inverse function is a retraction

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  (x : ℝ l)
  where

  abstract opaque
    unfolding
      map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ

    leq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      leq-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( x)))
        ( x)
    leq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
      in
        leq-leq-rational-ℝ _ _
          ( λ q x≤q →
            leq-not-le-ℝ _ _
              ( λ fq<fx →
                not-le-leq-ℝ
                  ( map-f x)
                  ( map-f (raise-real-ℚ l q))
                  ( is-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                    ( f)
                    ( x)
                    ( raise-real-ℚ l q)
                    ( preserves-leq-right-raise-ℝ l x≤q))
                  ( is-in-lower-cut-le-real-ℚ _ fq<fx)))

    geq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      leq-ℝ
        ( x)
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( x)))
    geq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
      in
        leq-leq-rational-ℝ _ _
          ( λ q f⁻¹fx≤q →
            leq-not-le-ℝ _ _
              ( λ q<x →
                not-leq-le-ℝ
                  ( real-ℚ q)
                  ( _)
                  ( le-real-is-in-lower-cut-ℝ _
                    ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                      ( f)
                      ( raise-real-ℚ l q)
                      ( x)
                      ( preserves-le-left-raise-ℝ l q<x)))
                  ( f⁻¹fx≤q)))

    is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( x)) ＝
      x
    is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      antisymmetric-leq-ℝ _ _
        ( leq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
        ( geq-is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

### The inverse function is strictly increasing

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  abstract opaque
    unfolding
      le-ℝ
      map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ

    is-strictly-increasing-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-strictly-increasing-endomap-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
    is-strictly-increasing-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      y y' y<y' =
      let
        x =
          map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( y)
        x' =
          map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( y')
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open do-syntax-trunc-Prop (le-prop-ℝ x x')
      in do
        (ε , y+ε<y') ←
          exists-positive-rational-separation-le-ℝ {l} {l} {y} {y'} y<y'
        (ε' , 2ε'<ε) ← double-le-ℚ⁺ ε
        (δ , Hδ) ←
          is-pointwise-ε-δ-continuous-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( x)
            ( ε')
        (p , fp<y , Nδxp) ← exists-rational-approximate-below-ℝ x δ
        (q , y<fq , Nδxq) ← exists-rational-approximate-above-ℝ x δ
        intro-exists
          ( q)
          ( y<fq ,
            concatenate-leq-le-ℝ
              ( map-f (raise-real-ℚ l q))
              ( y +ℝ real-ℚ⁺ ε)
              ( y')
              ( chain-of-inequalities
                map-f (raise-real-ℚ l q)
                ≤ map-f x +ℝ real-ℚ⁺ ε'
                  by
                    right-leq-real-bound-neighborhood-ℝ _ _ _
                      ( Hδ (raise-real-ℚ l q) Nδxq)
                ≤ map-f (raise-real-ℚ l p) +ℝ real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε'
                  by
                    preserves-leq-right-add-ℝ _ _ _
                      ( left-leq-real-bound-neighborhood-ℝ _ _ _
                        ( Hδ (raise-real-ℚ l p) Nδxp))
                ≤ map-f (raise-real-ℚ l p) +ℝ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                  by leq-eq-ℝ (associative-add-ℝ _ _ _)
                ≤ y +ℝ real-ℚ⁺ (ε' +ℚ⁺ ε')
                  by
                    preserves-leq-add-ℝ
                      ( leq-le-ℝ fp<y)
                      ( leq-eq-ℝ (add-real-ℚ _ _))
                ≤ y +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-left-add-ℝ _ _ _
                      ( preserves-leq-real-ℚ (leq-le-ℚ 2ε'<ε)))
              ( y+ε<y'))
```

### The inverse function is injective

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  abstract
    is-injective-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-injective
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
    is-injective-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      is-injective-is-strictly-increasing-endomap-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
        ( is-strictly-increasing-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
```

### The inverse function is a section

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  (y : ℝ l)
  where

  abstract
    is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( y)) ＝
      y
    is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
      is-injective-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( y)))
```

### A cofinal and coinitial, strictly increasing, pointwise ε-δ endomap on ℝ is an automorphism

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  is-equiv-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-equiv
      ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f))
  is-equiv-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-equiv-is-invertible
      ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f))
      ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f))
      ( is-retraction-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f))

  aut-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    Aut (ℝ l)
  aut-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    ( map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f) ,
      is-equiv-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

### The inverse function is cofinal

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  abstract
    is-cofinal-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-cofinal-endomap-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
    is-cofinal-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l)
              ( λ x →
                leq-prop-ℝ
                  ( real-ℚ q)
                  ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                    ( f)
                    ( x))))
      in do
        (r , fq<r) ← exists-greater-rational-ℝ (map-f (raise-real-ℚ l q))
        (x , r≤fx) ←
          is-cofinal-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( r)
        intro-exists
          ( map-f x)
          ( reflects-leq-left-raise-ℝ
            ( l)
            ( reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( raise-real-ℚ l q)
              ( _)
              ( inv-tr
                ( leq-ℝ _)
                ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                  ( f)
                  ( map-f x))
                ( transitive-leq-ℝ _ _ _ r≤fx (leq-le-ℝ fq<r)))))
```

### The inverse function is coinitial

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  abstract
    is-coinitial-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-coinitial-endomap-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
    is-coinitial-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      q =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l)
              ( λ x →
                leq-prop-ℝ
                  ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                    ( f)
                    ( x))
                  ( real-ℚ q)))
      in do
        (r , r<fq) ← exists-lesser-rational-ℝ (map-f (raise-real-ℚ l q))
        (x , fx≤r) ←
          is-coinitial-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( r)
        intro-exists
          ( map-f x)
          ( reflects-leq-right-raise-ℝ
            ( l)
            ( reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
              ( f)
              ( _)
              ( raise-real-ℚ l q)
              ( inv-tr
                ( λ z → leq-ℝ z (map-f (raise-real-ℚ l q)))
                ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                  ( f)
                  ( map-f x))
                ( transitive-leq-ℝ _ _ _ (leq-le-ℝ r<fq) fx≤r))))
```

### The inverse function is pointwise ε-δ continuous

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  abstract
    is-pointwise-ε-δ-continuous-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
      is-pointwise-ε-δ-continuous-endomap-ℝ
        ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f))
    is-pointwise-ε-δ-continuous-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      y ε =
      let
        map-f =
          map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        map-inv-f =
          map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
        x = map-inv-f y
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ⁺)
              ( λ δ →
                Π-Prop
                  ( ℝ l)
                  ( λ y' →
                    ( neighborhood-prop-ℝ l δ y y') ⇒
                    ( neighborhood-prop-ℝ l ε x (map-inv-f y')))))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        yhi = map-f (x +ℝ real-ℚ⁺ ε)
        ylo = map-f (x -ℝ real-ℚ⁺ ε)
      in do
        (δhi , y+δhi<yhi) ←
          exists-positive-rational-separation-le-ℝ
            ( tr
              ( λ y' → le-ℝ y' yhi)
              ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( y))
              ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( x)
                ( x +ℝ real-ℚ⁺ ε)
                ( le-left-add-real-ℚ⁺ x ε)))
        (δlo , ylo+δlo<y) ←
          exists-positive-rational-separation-le-ℝ
            ( tr
              ( le-ℝ ylo)
              ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( y))
              ( is-strictly-increasing-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( x -ℝ real-ℚ⁺ ε)
                ( x)
                ( le-diff-real-ℚ⁺ x ε)))
        intro-exists
          ( min-ℚ⁺ δlo δhi)
          ( λ y' Nδyy' →
            neighborhood-real-bound-each-leq-ℝ _ _ _
              ( leq-transpose-left-diff-ℝ _ _ _
                ( reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                  ( f)
                  ( x -ℝ real-ℚ⁺ ε)
                  ( map-inv-f y')
                  ( chain-of-inequalities
                    ylo
                    ≤ y -ℝ real-ℚ⁺ δlo
                      by leq-le-ℝ (le-transpose-left-add-ℝ _ _ _ ylo+δlo<y)
                    ≤ y -ℝ real-ℚ⁺ (min-ℚ⁺ δlo δhi)
                      by
                        reverses-leq-left-diff-ℝ
                          ( y)
                          ( preserves-leq-real-ℚ (leq-left-min-ℚ⁺ δlo δhi))
                    ≤ y'
                      by
                        leq-transpose-right-add-ℝ _ _ _
                          ( left-leq-real-bound-neighborhood-ℝ _ _ _ Nδyy')
                    ≤ map-f (map-inv-f y')
                      by
                        leq-eq-ℝ
                          ( inv
                            ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                              ( f)
                              ( y'))))))
              ( reflects-leq-map-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( map-inv-f y')
                ( x +ℝ real-ℚ⁺ ε)
                ( chain-of-inequalities
                  map-f (map-inv-f y')
                  ≤ y'
                    by
                      leq-eq-ℝ
                        ( is-section-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
                          ( f)
                          ( y'))
                  ≤ y +ℝ real-ℚ⁺ (min-ℚ⁺ δlo δhi)
                    by right-leq-real-bound-neighborhood-ℝ _ _ _ Nδyy'
                  ≤ y +ℝ real-ℚ⁺ δhi
                    by
                      preserves-leq-left-add-ℝ _ _ _
                        ( preserves-leq-real-ℚ (leq-right-min-ℚ⁺ δlo δhi))
                  ≤ yhi
                    by leq-le-ℝ y+δhi<yhi)))
```

### The inverse function is cofinal and coinitial, strictly increasing, and pointwise ε-δ continuous

```agda
module _
  {l : Level}
  (f :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l))
  where

  inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l)
  inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    ( ( ( map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f) ,
          is-pointwise-ε-δ-continuous-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)) ,
        is-strictly-increasing-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)) ,
      is-cofinal-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f) ,
      is-coinitial-map-inv-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( f))
```
