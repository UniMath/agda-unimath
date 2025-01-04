# Infinite conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.infinite-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A [conatural number](elementary-number-theory.conatural-numbers.md) `x` is
{{#concept "infinite" Disambiguation="conatural number" Agda=is-infinite-successor-condition-ℕ∞}}
if it is its own predecessor

```text
  decons-ℕ∞ x ＝ inl x
```

or, equivalently, if it is its own successor

```text
  x ＝ succ-ℕ∞ x.
```

## Definitions

### The predicate on conatural numbers of being infinite

```agda
is-infinite-ℕ∞ : ℕ∞ → UU lzero
is-infinite-ℕ∞ x = decons-ℕ∞ x ＝ inl x

is-infinite-successor-condition-ℕ∞ : ℕ∞ → UU lzero
is-infinite-successor-condition-ℕ∞ x = x ＝ succ-ℕ∞ x
```

## Properties

### blabla

```agda
is-infinite-is-infinite-successor-condition-ℕ∞ :
  (x : ℕ∞) → is-infinite-successor-condition-ℕ∞ x → is-infinite-ℕ∞ x
is-infinite-is-infinite-successor-condition-ℕ∞ x = ap decons-ℕ∞

is-infinite-successor-condition-cons-is-infinite-cons-ℕ∞ :
  (x : ℕ∞) →
  is-infinite-ℕ∞ (cons-ℕ∞ (decons-ℕ∞ x)) →
  is-infinite-successor-condition-ℕ∞ (cons-ℕ∞ (decons-ℕ∞ x))
is-infinite-successor-condition-cons-is-infinite-cons-ℕ∞ x =
  ind-coproduct
    ( λ y →
      is-infinite-ℕ∞ (cons-ℕ∞ y) →
      is-infinite-successor-condition-ℕ∞ (cons-ℕ∞ y))
    ( λ x' → ap cons-ℕ∞)
    ( λ x' → ap cons-ℕ∞)
    ( decons-ℕ∞ x)
```

### The point at infinity is unique

```text
eq-is-infinite-successor-condition-ℕ∞ :
  (x y : ℕ∞) →
  is-infinite-successor-condition-ℕ∞ x →
  is-infinite-successor-condition-ℕ∞ y →
  x ＝ y
eq-is-infinite-successor-condition-ℕ∞ x y p q =
```

### The point at infinity is infinite

```agda
is-infinite-infinity-ℕ∞ : is-infinite-ℕ∞ infinity-ℕ∞
is-infinite-infinity-ℕ∞ = refl
```
