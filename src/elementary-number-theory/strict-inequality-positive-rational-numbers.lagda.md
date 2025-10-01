# Strict inequality on positive rational numbers

```agda
module elementary-number-theory.strict-inequality-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="positive rational numbers" Agda=le-ℚ⁺}}
on the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is inherited from the
[standard strict ordering](elementary-number-theory.strict-inequality-rational-numbers.md)
on [rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
le-prop-ℚ⁺ : ℚ⁺ → ℚ⁺ → Prop lzero
le-prop-ℚ⁺ x y = le-ℚ-Prop (rational-ℚ⁺ x) (rational-ℚ⁺ y)

le-ℚ⁺ : ℚ⁺ → ℚ⁺ → UU lzero
le-ℚ⁺ x y = type-Prop (le-prop-ℚ⁺ x y)

is-prop-le-ℚ⁺ : (x y : ℚ⁺) → is-prop (le-ℚ⁺ x y)
is-prop-le-ℚ⁺ x y = is-prop-type-Prop (le-prop-ℚ⁺ x y)
```

## Properties

### Strict inequality is transitive

```agda
transitive-le-ℚ⁺ : is-transitive le-ℚ⁺
transitive-le-ℚ⁺ x y z =
  transitive-le-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y) (rational-ℚ⁺ z)
```

### If `a < b`, then `a ≤ b`

```agda
leq-le-ℚ⁺ : {x y : ℚ⁺} → le-ℚ⁺ x y → leq-ℚ⁺ x y
leq-le-ℚ⁺ {x} {y} = leq-le-ℚ {rational-ℚ⁺ x} {rational-ℚ⁺ y}
```

### The strictly preordered set of positive rational numbers

```agda
strictly-preordered-set-ℚ⁺ : Strictly-Preordered-Set lzero lzero
pr1 strictly-preordered-set-ℚ⁺ = set-ℚ⁺
pr2 strictly-preordered-set-ℚ⁺ =
  ( le-prop-ℚ⁺) ,
  ( irreflexive-le-ℚ ∘ rational-ℚ⁺) ,
  ( transitive-le-ℚ⁺)

strict-preorder-ℚ⁺ : Strict-Preorder lzero lzero
strict-preorder-ℚ⁺ =
  strict-preorder-Strictly-Preordered-Set strictly-preordered-set-ℚ⁺
```

### There is no least positive rational number

```agda
opaque
  mediant-zero-ℚ⁺ : ℚ⁺ → ℚ⁺
  mediant-zero-ℚ⁺ x =
    ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x) ,
      is-positive-le-zero-ℚ
        ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x))
        ( le-left-mediant-ℚ
          ( zero-ℚ)
          ( rational-ℚ⁺ x)
          ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))))

  le-mediant-zero-ℚ⁺ : (x : ℚ⁺) → le-ℚ⁺ (mediant-zero-ℚ⁺ x) x
  le-mediant-zero-ℚ⁺ x =
    le-right-mediant-ℚ
      ( zero-ℚ)
      ( rational-ℚ⁺ x)
      ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))
```
