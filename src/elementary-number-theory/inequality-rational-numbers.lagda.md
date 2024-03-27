# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="rational numbers" Agda=leq-ℚ}} on the
[rational numbers](elementary-number-theory.rational-numbers.md) is inherited from the [standard ordering](elementary-number-theory.inequality-integer-fractions.md) on [integer fractions](elementary-number-theory.integer-fractions.md): the rational number `m / n` is _less than or equal to_ `m' / n'` if the [integer product](elementary-number-theory.multiplication-integers.md) `m * n'` is [less than or equal](elementary-number-theory.inequality-integers.md) to `m' * n`.

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Prop : ℚ → ℚ → Prop lzero
leq-ℚ-Prop (x , px) (y , py) = leq-fraction-ℤ-Prop x y

leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ x y = type-Prop (leq-ℚ-Prop x y)

is-prop-leq-ℚ : (x y : ℚ) → is-prop (leq-ℚ x y)
is-prop-leq-ℚ x y = is-prop-type-Prop (leq-ℚ-Prop x y)

infix 30 _≤-ℚ_
_≤-ℚ_ = leq-ℚ
```

## Properties

### Inequality of rational numbers is decidable

```agda
is-decidable-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + ¬ (leq-ℚ x y)
is-decidable-leq-ℚ x y =
  is-decidable-leq-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

leq-ℚ-Decidable-Prop : (x y : ℚ) → Decidable-Prop lzero
leq-ℚ-Decidable-Prop x y =
  ( leq-ℚ x y ,
    is-prop-leq-ℚ x y ,
    is-decidable-leq-ℚ x y)
```

### Inequality on rational numbers is reflexive

```agda
refl-leq-ℚ : (x : ℚ) → leq-ℚ x x
refl-leq-ℚ x =
  refl-leq-ℤ (numerator-ℚ x *ℤ denominator-ℚ x)
```

### Inequality on rational numbers is antisymmetric

```agda
antisymmetric-leq-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℚ y x → x ＝ y
antisymmetric-leq-ℚ x y H H' =
  ( inv (in-fraction-fraction-ℚ x)) ∙
  ( eq-ℚ-sim-fraction-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)
    ( is-sim-antisymmetric-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( H)
      ( H'))) ∙
  ( in-fraction-fraction-ℚ y)
```

### The standard ordering on rational numbers is linear

```agda
linear-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + (leq-ℚ y x)
linear-leq-ℚ x y =
  map-coproduct
    ( id)
    ( is-nonnegative-eq-ℤ
      (distributive-neg-diff-ℤ
        ( numerator-ℚ y *ℤ denominator-ℚ x)
        ( numerator-ℚ x *ℤ denominator-ℚ y)))
    ( decide-is-nonnegative-is-nonnegative-neg-ℤ
      { cross-mul-diff-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)})
```

### Transitivity properties

```agda
module _
  (x y z : ℚ)
  where

  transitive-leq-ℚ : leq-ℚ y z → leq-ℚ x y → leq-ℚ x z
  transitive-leq-ℚ =
    transitive-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)
```

### The partially ordered set of rational numbers given by the standard ordering

```agda
ℚ-Preorder : Preorder lzero lzero
ℚ-Preorder =
  (ℚ , leq-ℚ-Prop , refl-leq-ℚ , transitive-leq-ℚ)

ℚ-Poset : Poset lzero lzero
ℚ-Poset = (ℚ-Preorder , antisymmetric-leq-ℚ)
```

## See also

- The decidable total order on the rational numbers is defined in
  [`decidable-total-order-rational-numbers](elementary-number-theory.decidable-total-order-rational-numbers.md)
- The strict ordering on the rational numbers is defined in
  [`strict-inequality-rational-numbers`](elementary-number-theory.strict-inequality-rational-numbers.md)
