# The minimum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="binary, Dedekind real numbers" Agda=min-ℝ WD="minimum" WDID=Q10585806}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    min-ℝ : ℝ (l1 ⊔ l2)
    min-ℝ = neg-ℝ (max-ℝ (neg-ℝ x) (neg-ℝ y))
```

## Properties

### The binary minimum is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding min-ℝ

    is-greatest-binary-lower-bound-min-ℝ :
      is-greatest-binary-lower-bound-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( y)
        ( min-ℝ x y)
    pr1 (is-greatest-binary-lower-bound-min-ℝ z) (z≤x , z≤y) =
      tr
        ( λ w → leq-ℝ w (min-ℝ x y))
        ( neg-neg-ℝ z)
        ( neg-leq-ℝ (max-ℝ (neg-ℝ x) (neg-ℝ y)) (neg-ℝ z)
          ( forward-implication
            ( is-least-binary-upper-bound-max-ℝ (neg-ℝ x) (neg-ℝ y) (neg-ℝ z))
            ( neg-leq-ℝ z x z≤x , neg-leq-ℝ z y z≤y)))
    pr1 (pr2 (is-greatest-binary-lower-bound-min-ℝ z) z≤min) =
      transitive-leq-ℝ z (min-ℝ x y) x
        ( tr
          ( leq-ℝ (min-ℝ x y))
          ( neg-neg-ℝ _)
          ( neg-leq-ℝ (neg-ℝ x) (max-ℝ (neg-ℝ x) (neg-ℝ y))
            ( leq-left-max-ℝ (neg-ℝ x) (neg-ℝ y))))
        ( z≤min)
    pr2 (pr2 (is-greatest-binary-lower-bound-min-ℝ z) z≤min) =
      transitive-leq-ℝ z (min-ℝ x y) y
        ( tr
          ( leq-ℝ (min-ℝ x y))
          ( neg-neg-ℝ _)
          ( neg-leq-ℝ (neg-ℝ y) (max-ℝ (neg-ℝ x) (neg-ℝ y))
            ( leq-right-max-ℝ (neg-ℝ x) (neg-ℝ y))))
        ( z≤min)

  abstract
    leq-min-leq-leq-ℝ :
      {l3 : Level} (z : ℝ l3) → leq-ℝ z x → leq-ℝ z y → leq-ℝ z (min-ℝ x y)
    leq-min-leq-leq-ℝ z x≤z y≤z =
      forward-implication (is-greatest-binary-lower-bound-min-ℝ z) (x≤z , y≤z)
```

### The large poset of real numbers has meets

```agda
has-meets-ℝ-Large-Poset : has-meets-Large-Poset ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-ℝ-Large-Poset = min-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-ℝ-Large-Poset = is-greatest-binary-lower-bound-min-ℝ
```

### For any `ε : ℚ⁺`, `(x < min-ℝ x y + ε) ∨ (y < min-ℝ x y + ε)`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding min-ℝ

    approximate-above-min-ℝ :
      (ε : ℚ⁺) →
      type-disjunction-Prop
        ( le-ℝ-Prop x (min-ℝ x y +ℝ real-ℚ⁺ ε))
        ( le-ℝ-Prop y (min-ℝ x y +ℝ real-ℚ⁺ ε))
    approximate-above-min-ℝ ε =
      elim-disjunction
        ( (le-ℝ-Prop x (min-ℝ x y +ℝ real-ℚ⁺ ε)) ∨
          (le-ℝ-Prop y (min-ℝ x y +ℝ real-ℚ⁺ ε)))
        ( λ max-ε<-x →
          inl-disjunction
            ( binary-tr le-ℝ
              ( neg-neg-ℝ x)
              ( distributive-neg-diff-ℝ _ _ ∙ commutative-add-ℝ _ _)
              ( neg-le-ℝ
                ( max-ℝ (neg-ℝ x) (neg-ℝ y) -ℝ real-ℚ⁺ ε)
                ( neg-ℝ x)
                ( max-ε<-x))))
        ( λ max-ε<-y →
          inr-disjunction
            ( binary-tr le-ℝ
              ( neg-neg-ℝ y)
              ( distributive-neg-diff-ℝ _ _ ∙ commutative-add-ℝ _ _)
              ( neg-le-ℝ
                ( max-ℝ (neg-ℝ x) (neg-ℝ y) -ℝ real-ℚ⁺ ε)
                ( neg-ℝ y)
                ( max-ε<-y))))
        ( approximate-below-max-ℝ (neg-ℝ x) (neg-ℝ y) ε)
```
