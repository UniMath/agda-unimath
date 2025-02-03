# Infinite conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.infinite-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.equality-conatural-numbers

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

or, [equivalently](foundation-core.equivalences.md), if it is its own successor

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

### The two definitions of being infinite agree

```agda
is-infinite-is-infinite-successor-condition-ℕ∞ :
  {x : ℕ∞} → is-infinite-successor-condition-ℕ∞ x → is-infinite-ℕ∞ x
is-infinite-is-infinite-successor-condition-ℕ∞ = ap decons-ℕ∞

is-infinite-successor-condition-is-infinite-ℕ∞ :
  {x : ℕ∞} → is-infinite-ℕ∞ x → is-infinite-successor-condition-ℕ∞ x
is-infinite-successor-condition-is-infinite-ℕ∞ = is-injective-decons-ℕ∞
```

### The point at infinity is infinite

```agda
is-infinite-infinity-ℕ∞ : is-infinite-ℕ∞ infinity-ℕ∞
is-infinite-infinity-ℕ∞ = refl

is-infinite-successor-condition-infinity-ℕ∞ :
  is-infinite-successor-condition-ℕ∞ infinity-ℕ∞
is-infinite-successor-condition-infinity-ℕ∞ =
  is-infinite-successor-condition-is-infinite-ℕ∞ is-infinite-infinity-ℕ∞
```
