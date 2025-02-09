# The canonical inclusion of natural numbers into increasing binary sequences

```agda
module set-theory.inclusion-natural-numbers-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import logic.double-negation-eliminating-maps
open import logic.irrefutably-surjective-maps

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
open import set-theory.finite-elements-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
```

</details>

## Idea

The canonical map `ℕ → ℕ∞↑` defined by induction to send zero to zero, and the
successor of `n` to the successor of the map evaluated at `n` is the
{{#concept "canonical inclusion" Disambiguaiton="of the natural numbers into increasing binary sequences" Agda=inclusion-ℕ∞↑-ℕ}}.
This map is a [embedding](foundation-core.embeddings.md) of
[sets](foundation-core.sets.md) that is
non-[surjective](foundation.surjective-maps.md), as it does not hit the element
at infinity. We may extend this inclusion by adding a point at infinity

```text
  ℕ + {∞} ↪ ℕ∞↑
```

to obtain a [dense](logic.irrefutably-surjective-maps.md) embedding of sets.
This map is surjective if and only if the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
holds.

## Definitions

### The canonical inclusion of natural numbers

```agda
inclusion-ℕ∞↑-ℕ : ℕ → ℕ∞↑
inclusion-ℕ∞↑-ℕ = rec-ℕ zero-ℕ∞↑ (λ _ → succ-ℕ∞↑)
```

### The canonical extended inclusion

```agda
inclusion-ℕ∞↑-Maybe-ℕ : Maybe ℕ → ℕ∞↑
inclusion-ℕ∞↑-Maybe-ℕ = rec-coproduct inclusion-ℕ∞↑-ℕ (point infinity-ℕ∞↑)
```

## Properties

### The canonical inclusion is an embedding

```agda
abstract
  is-injective-inclusion-ℕ∞↑-ℕ : is-injective inclusion-ℕ∞↑-ℕ
  is-injective-inclusion-ℕ∞↑-ℕ {zero-ℕ} {zero-ℕ} p =
    refl
  is-injective-inclusion-ℕ∞↑-ℕ {zero-ℕ} {succ-ℕ y} p =
    ex-falso (neq-zero-succ-ℕ∞↑ p)
  is-injective-inclusion-ℕ∞↑-ℕ {succ-ℕ x} {zero-ℕ} p =
    ex-falso (neq-succ-zero-ℕ∞↑ p)
  is-injective-inclusion-ℕ∞↑-ℕ {succ-ℕ x} {succ-ℕ y} p =
    ap succ-ℕ (is-injective-inclusion-ℕ∞↑-ℕ (is-injective-succ-ℕ∞↑ p))

abstract
  is-emb-inclusion-ℕ∞↑-ℕ : is-emb inclusion-ℕ∞↑-ℕ
  is-emb-inclusion-ℕ∞↑-ℕ =
    is-emb-is-injective is-set-ℕ∞↑ is-injective-inclusion-ℕ∞↑-ℕ
```

### The canonical inclusion is double negation stable

> Needs case analysis on infinity

```agda
-- double-negation-elim-inclusion-ℕ∞↑-ℕ :
--   is-double-negation-eliminating-map inclusion-ℕ∞↑-ℕ
-- double-negation-elim-inclusion-ℕ∞↑-ℕ x = {!   !}
```

### The canonical inclusion preserves order

```agda
abstract
  preserves-order-inclusion-ℕ∞↑-ℕ :
    preserves-order-Poset ℕ-Poset ℕ∞↑-Poset inclusion-ℕ∞↑-ℕ
  preserves-order-inclusion-ℕ∞↑-ℕ zero-ℕ y p =
    leq-zero-ℕ∞↑ (inclusion-ℕ∞↑-ℕ y)
  preserves-order-inclusion-ℕ∞↑-ℕ
    ( succ-ℕ x) (succ-ℕ y) p =
    preserves-order-succ-ℕ∞↑
      ( inclusion-ℕ∞↑-ℕ x)
      ( inclusion-ℕ∞↑-ℕ y)
      ( preserves-order-inclusion-ℕ∞↑-ℕ x y p)
```

### If an increasing binary sequence changes from false to true at position `n`, then it is in the image of the canonical inclusion

```agda
leq-inclusion-ℕ∞↑-ℕ-leq-ℕ-ℕ∞↑ :
    (x : ℕ∞↑) (n : ℕ) → x ≤-ℕ∞↑-ℕ n → x ≤-ℕ∞↑ (inclusion-ℕ∞↑-ℕ n)
leq-inclusion-ℕ∞↑-ℕ-leq-ℕ-ℕ∞↑ x zero-ℕ p zero-ℕ =
  leq-eq-bool {true} {sequence-ℕ∞↑ x zero-ℕ} (inv p)
leq-inclusion-ℕ∞↑-ℕ-leq-ℕ-ℕ∞↑ x zero-ℕ p (succ-ℕ i) =
  {! leq-inclusion-ℕ∞↑-ℕ-leq-ℕ-ℕ∞↑ x zero-ℕ p i  !}
leq-inclusion-ℕ∞↑-ℕ-leq-ℕ-ℕ∞↑ x (succ-ℕ n) p i = {!   !}

abstract
  Eq-inclusion-ℕ∞↑-ℕ :
    (x : ℕ∞↑) (n : ℕ) →
    ¬ (x ≤-ℕ∞↑-ℕ n) → x ≤-ℕ∞↑-ℕ (succ-ℕ n) →
    Eq-ℕ∞↑ x (inclusion-ℕ∞↑-ℕ (succ-ℕ n))
  Eq-inclusion-ℕ∞↑-ℕ x zero-ℕ np p zero-ℕ =
    is-false-is-not-true (pr1 x 0) np
  Eq-inclusion-ℕ∞↑-ℕ x zero-ℕ np p (succ-ℕ k) =
    Eq-leq-zero-ℕ∞↑ (pr1 x ∘ succ-ℕ , pr2 x ∘ succ-ℕ) (λ n → {! p   !}) k
  Eq-inclusion-ℕ∞↑-ℕ x (succ-ℕ n) np p = {!   !}

-- abstract
--   eq-zero-is-zero-ℕ∞↑ :
--     (x : ℕ∞↑) →
--     is-true (sequence-ℕ∞↑ x 0) →
--     x ＝ zero-ℕ∞↑
--   eq-zero-is-zero-ℕ∞↑ x p =
--     eq-Eq-ℕ∞↑
--       ( Eq-zero-is-zero-ℕ∞↑ x p)
```

### If an increasing binary sequence is not in the image of the canonical inclusion then it is infinity

```agda
module _
  (x : ℕ∞↑)
  (H : (n : ℕ) → x ≠ inclusion-ℕ∞↑-ℕ n)
  where

  Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ :
    sequence-ℕ∞↑ x ~ const ℕ false
  Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ zero-ℕ =
    is-false-is-not-true (sequence-ℕ∞↑ x 0) λ t → H 0 {!   !}
  Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ (succ-ℕ n) = {!   !}

  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ :
    x ＝ infinity-ℕ∞↑
  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ =
    eq-Eq-ℕ∞↑
      ( Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ)
```

### The canonical inclusion is not surjective

### The canonical extended inclusion is an embedding

```agda
abstract
  is-emb-inclusion-ℕ∞↑-Maybe-ℕ : is-emb inclusion-ℕ∞↑-Maybe-ℕ
  is-emb-inclusion-ℕ∞↑-Maybe-ℕ =
    is-emb-coproduct is-emb-inclusion-ℕ∞↑-ℕ (is-emb-is-injective is-set-ℕ∞↑ (is-injective-point infinity-ℕ∞↑)) {!   !}
```

### The canonical extended inclusion is irrefutably surjective

```agda
is-irrefutably-surjective-inclusion-ℕ∞↑-Maybe-ℕ :
  is-irrefutably-surjective inclusion-ℕ∞↑-Maybe-ℕ
is-irrefutably-surjective-inclusion-ℕ∞↑-Maybe-ℕ x np =
  g (eq-infinity-is-not-finitely-bounded-ℕ∞↑ x λ n → map-neg {!   !} (h n)) -- TODO: need succ condition
  where
  g : ¬ (x ＝ infinity-ℕ∞↑)
  g p = np (exception-Maybe , inv p)

  h : (n : ℕ) → ¬ (x ＝ inclusion-ℕ∞↑-ℕ n)
  h n p = np (inl n , inv p)
```

### An increasing binary sequence is finitely bounded if and only if it is less than an increasing binary sequence in the image of the natural numbers

> This remains to be formalized.
