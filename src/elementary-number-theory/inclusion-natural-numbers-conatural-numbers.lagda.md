# The inclusion of the natural numbers into the conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.inclusion-natural-numbers-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.infinite-conatural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.surjective-maps

open import foundation-core.empty-types
open import foundation-core.identity-types

open import logic.double-negation-dense-maps

open import set-theory.equivalence-conatural-numbers-increasing-binary-sequences
open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

The
{{#concept "inclusion of the nautural numbers into the conatural numbers" Agda=conatural-ℕ}}
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

### The canonical extended inclusion into the conatural numbers

```agda
conatural-number-ℕ+∞ : Maybe ℕ → ℕ∞
conatural-number-ℕ+∞ = rec-coproduct conatural-ℕ (λ _ → infinity-ℕ∞)
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
  ap succ-ℕ (is-injective-conatural-ℕ (is-injective-succ-ℕ∞ p))
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

is-not-surjective-conatural-ℕ : ¬ is-surjective conatural-ℕ
is-not-surjective-conatural-ℕ H =
  elim-exists empty-Prop neq-infinity-conatural-ℕ (H infinity-ℕ∞)
```

### The canonical inclusion is homotopic to the composite through increasing binary sequences

```agda
abstract
  htpy-conatural-number-increasing-binary-sequence-ℕ :
    conatural-number-ℕ∞↗ ∘ increasing-binary-sequence-ℕ ~ conatural-ℕ
  htpy-conatural-number-increasing-binary-sequence-ℕ zero-ℕ =
    compute-conatural-number-zero-ℕ∞↗
  htpy-conatural-number-increasing-binary-sequence-ℕ (succ-ℕ n) =
    ( compute-conatural-number-ℕ∞↗-succ (increasing-binary-sequence-ℕ n)) ∙
    ( ap succ-ℕ∞ (htpy-conatural-number-increasing-binary-sequence-ℕ n))
```

### The canonical extended inclusion is homotopic to the composite through increasing binary sequences

```agda
abstract
  htpy-conatural-number-ℕ+∞ :
    conatural-number-ℕ∞↗ ∘ increasing-binary-sequence-ℕ+∞ ~ conatural-number-ℕ+∞
  htpy-conatural-number-ℕ+∞ (inl n) =
    htpy-conatural-number-increasing-binary-sequence-ℕ n
  htpy-conatural-number-ℕ+∞ (inr _) =
    compute-conatural-number-infinity-ℕ∞↗
```

### The canonical extended inclusion is a double negation dense embedding

```agda
abstract
  is-emb-conatural-number-ℕ+∞ : is-emb conatural-number-ℕ+∞
  is-emb-conatural-number-ℕ+∞ =
    is-emb-left-map-triangle
      ( conatural-number-ℕ+∞)
      ( conatural-number-ℕ∞↗)
      ( increasing-binary-sequence-ℕ+∞)
      ( inv-htpy htpy-conatural-number-ℕ+∞)
      ( is-emb-equiv equiv-conatural-number-ℕ∞↗)
      ( is-emb-increasing-binary-sequence-ℕ+∞)

emb-conatural-number-ℕ+∞ : Maybe ℕ ↪ ℕ∞
emb-conatural-number-ℕ+∞ =
  ( conatural-number-ℕ+∞ , is-emb-conatural-number-ℕ+∞)

abstract
  is-double-negation-dense-conatural-number-ℕ+∞ :
    is-double-negation-dense-map conatural-number-ℕ+∞
  is-double-negation-dense-conatural-number-ℕ+∞ =
    is-double-negation-dense-map-left-map-triangle
      ( conatural-number-ℕ+∞)
      ( conatural-number-ℕ∞↗)
      ( increasing-binary-sequence-ℕ+∞)
      ( inv-htpy htpy-conatural-number-ℕ+∞)
      ( is-double-negation-dense-map-equiv equiv-conatural-number-ℕ∞↗)
      ( is-double-negation-dense-increasing-binary-sequence-ℕ+∞)

double-negation-dense-conatural-number-ℕ+∞ : Maybe ℕ ↠¬¬ ℕ∞
double-negation-dense-conatural-number-ℕ+∞ =
  ( conatural-number-ℕ+∞ ,
    is-double-negation-dense-conatural-number-ℕ+∞)
```
