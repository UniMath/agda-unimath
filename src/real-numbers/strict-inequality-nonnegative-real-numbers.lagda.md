# Strict inequality of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-nonnegative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="on the nonnegative real numbers" Agda=le-ℝ⁰⁺}}
on the [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
inherited from the
[standard strict ordering](real-numbers.strict-inequality-real-numbers.md) on
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
le-prop-ℝ⁰⁺ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → Prop (l1 ⊔ l2)
le-prop-ℝ⁰⁺ x y = le-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

le-ℝ⁰⁺ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → UU (l1 ⊔ l2)
le-ℝ⁰⁺ x y = type-Prop (le-prop-ℝ⁰⁺ x y)

is-prop-le-ℝ⁰⁺ :
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → is-prop (le-ℝ⁰⁺ x y)
is-prop-le-ℝ⁰⁺ x y = is-prop-type-Prop (le-prop-ℝ⁰⁺ x y)
```

## Properties

### The canonical embedding of nonnegative rational numbers to nonnegative reals preserves strict inequality

```agda
abstract
  preserves-le-nonnegative-real-ℚ⁰⁺ :
    (p q : ℚ⁰⁺) →
    le-ℚ⁰⁺ p q → le-ℝ⁰⁺ (nonnegative-real-ℚ⁰⁺ p) (nonnegative-real-ℚ⁰⁺ q)
  preserves-le-nonnegative-real-ℚ⁰⁺ p q = preserves-le-real-ℚ _ _
```

### Similarity preserves strict inequality

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ⁰⁺ l1) (x : ℝ⁰⁺ l2) (y : ℝ⁰⁺ l3) (x~y : sim-ℝ⁰⁺ x y)
  where

  abstract
    preserves-le-left-sim-ℝ⁰⁺ : le-ℝ⁰⁺ x z → le-ℝ⁰⁺ y z
    preserves-le-left-sim-ℝ⁰⁺ =
      preserves-le-left-sim-ℝ (real-ℝ⁰⁺ z) _ _ x~y
```

### Addition preserves strict inequality

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) (w : ℝ⁰⁺ l4)
  where

  abstract
    preserves-le-add-ℝ⁰⁺ :
      le-ℝ⁰⁺ x y → le-ℝ⁰⁺ z w → le-ℝ⁰⁺ (x +ℝ⁰⁺ z) (y +ℝ⁰⁺ w)
    preserves-le-add-ℝ⁰⁺ =
      preserves-le-add-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z) (real-ℝ⁰⁺ w)
```

### Concatenation of inequality and strict inequality

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3)
  where

  abstract
    concatenate-leq-le-ℝ⁰⁺ : leq-ℝ⁰⁺ x y → le-ℝ⁰⁺ y z → le-ℝ⁰⁺ x z
    concatenate-leq-le-ℝ⁰⁺ =
      concatenate-leq-le-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z)
```

### Every nonnegative real number is less than some positive rational number

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  abstract
    le-some-positive-rational-ℝ⁰⁺ :
      exists ℚ⁺ (λ q → le-prop-ℝ⁰⁺ x (nonnegative-real-ℚ⁺ q))
    le-some-positive-rational-ℝ⁰⁺ =
      map-tot-exists
        ( λ (q , _) x<q → le-real-is-in-upper-cut-ℚ q (real-ℝ⁰⁺ x) x<q)
        ( exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ x)
```
