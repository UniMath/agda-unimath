# The inclusion of the natural numbers into the conatural numbers

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.inclusion-natural-numbers-conatural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers funext univalence truncations
open import elementary-number-theory.infinite-conatural-numbers funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.existential-quantification funext univalence truncations
open import foundation.injective-maps funext
open import foundation.negated-equality funext univalence truncations
open import foundation.negation funext
open import foundation.surjective-maps funext univalence truncations

open import foundation-core.empty-types
open import foundation-core.identity-types
```

</details>

## Idea

The
{{#concept "inclusion of the nautural numbers into the conatural numbers" Agda=ℕ∞}}
is the inductively defined map

```text
  conatural-ℕ : ℕ → ℕ∞
```

that sends zero to zero, and the successor of a natural number to the successor
of its inclusion.

## Definitions

### The canonical inclusion of the natural numbers into the conatural numbers

```agda
conatural-ℕ : ℕ → ℕ∞
conatural-ℕ zero-ℕ = zero-ℕ∞
conatural-ℕ (succ-ℕ x) = succ-ℕ∞ (conatural-ℕ x)
```

## Properties

### The canonical inclusion of the natural numbers is injective

```agda
is-injective-conatural-ℕ : is-injective conatural-ℕ
is-injective-conatural-ℕ {zero-ℕ} {zero-ℕ} p = refl
is-injective-conatural-ℕ {zero-ℕ} {succ-ℕ y} p =
  ex-falso (neq-zero-succ-ℕ∞ (conatural-ℕ y) (inv p))
is-injective-conatural-ℕ {succ-ℕ x} {zero-ℕ} p =
  ex-falso (neq-zero-succ-ℕ∞ (conatural-ℕ x) p)
is-injective-conatural-ℕ {succ-ℕ x} {succ-ℕ y} p =
  ap succ-ℕ (is-injective-conatural-ℕ {x} {y} (is-injective-succ-ℕ∞ p))
```

### The canonical inclusion of the natural numbers is not surjective

The canonical inclusion of the natural numbers is not surjective because it does
not hit the point at infinity.

```agda
neq-infinity-conatural-ℕ : (n : ℕ) → conatural-ℕ n ≠ infinity-ℕ∞
neq-infinity-conatural-ℕ zero-ℕ = neq-infinity-zero-ℕ∞
neq-infinity-conatural-ℕ (succ-ℕ n) p =
  neq-infinity-conatural-ℕ n
    ( is-injective-succ-ℕ∞ (p ∙ is-infinite-successor-condition-infinity-ℕ∞))

is-not-surjective-conatural-ℕ : ¬ (is-surjective conatural-ℕ)
is-not-surjective-conatural-ℕ H =
  elim-exists empty-Prop neq-infinity-conatural-ℕ (H infinity-ℕ∞)
```
