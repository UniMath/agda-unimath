# Nonzero integers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.nonzero-integers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

An [integer](elementary-number-theory.integers.md) `k` is said to be **nonzero**
if the [proposition](foundation.propositions.md)

```text
  k ≠ 0
```

holds.

## Definition

### The predicate of being a nonzero integer

```agda
is-nonzero-prop-ℤ : ℤ → Prop lzero
is-nonzero-prop-ℤ k = neg-type-Prop (k ＝ zero-ℤ)

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = type-Prop (is-nonzero-prop-ℤ k)

is-prop-is-nonzero-ℤ : (k : ℤ) → is-prop (is-nonzero-ℤ k)
is-prop-is-nonzero-ℤ k = is-prop-type-Prop (is-nonzero-prop-ℤ k)
```

### The nonzero integers

```agda
nonzero-ℤ : UU lzero
nonzero-ℤ = type-subtype is-nonzero-prop-ℤ

module _
  (k : nonzero-ℤ)
  where

  int-nonzero-ℤ : ℤ
  int-nonzero-ℤ = pr1 k

  is-nonzero-nonzero-ℤ : is-nonzero-ℤ int-nonzero-ℤ
  is-nonzero-nonzero-ℤ = pr2 k
```

### The nonzero integer `1`

```agda
is-nonzero-one-ℤ : is-nonzero-ℤ one-ℤ
is-nonzero-one-ℤ ()

one-nonzero-ℤ : nonzero-ℤ
pr1 one-nonzero-ℤ = one-ℤ
pr2 one-nonzero-ℤ = is-nonzero-one-ℤ
```

## Properties

### The integer image of a nonzero natural number is nonzero

```agda
is-nonzero-int-ℕ : (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℤ (int-ℕ n)
is-nonzero-int-ℕ zero-ℕ H p = H refl
```

### The negative of a nonzero integer is nonzero

```agda
is-nonzero-neg-nonzero-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-nonzero-ℤ (neg-ℤ x)
is-nonzero-neg-nonzero-ℤ x H K = H (is-zero-is-zero-neg-ℤ x K)
```
