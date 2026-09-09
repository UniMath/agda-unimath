# Finite elements in the type of increasing binary sequences

```agda
module set-theory.finite-elements-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.constant-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.identity-types

open import set-theory.increasing-binary-sequences
```

</details>

## Idea

An [increasing binary sequence](set-theory.increasing-binary-sequences.md) `x`
is a
{{#concept "finite element" Disambiguation="element of the type of increasing binary sequences" Agda=is-finite-ℕ∞↗}}
if there [exists](foundation.existential-quantification.md) a
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ` such that
`xₙ` is true.

## Definitions

### Finite boundedness of increasing binary sequences

```agda
is-finitely-bounded-decidable-prop-ℕ∞↗ : ℕ∞↗ → ℕ → Decidable-Prop lzero
is-finitely-bounded-decidable-prop-ℕ∞↗ x n =
  is-true-Decidable-Prop (sequence-ℕ∞↗ x n)

is-finitely-bounded-prop-ℕ∞↗ : ℕ∞↗ → ℕ → Prop lzero
is-finitely-bounded-prop-ℕ∞↗ x n =
  prop-Decidable-Prop
    ( is-finitely-bounded-decidable-prop-ℕ∞↗ x n)

is-finitely-bounded-ℕ∞↗ : ℕ∞↗ → ℕ → UU lzero
is-finitely-bounded-ℕ∞↗ x n =
  type-Decidable-Prop
    ( is-finitely-bounded-decidable-prop-ℕ∞↗ x n)

is-prop-is-finitely-bounded-ℕ∞↗ :
  (x : ℕ∞↗) (n : ℕ) → is-prop (is-finitely-bounded-ℕ∞↗ x n)
is-prop-is-finitely-bounded-ℕ∞↗ x n =
  is-prop-type-Decidable-Prop
    ( is-finitely-bounded-decidable-prop-ℕ∞↗ x n)

is-decidable-is-finitely-bounded-ℕ∞↗ :
  (x : ℕ∞↗) (n : ℕ) → is-decidable (is-finitely-bounded-ℕ∞↗ x n)
is-decidable-is-finitely-bounded-ℕ∞↗ x n =
  is-decidable-Decidable-Prop (is-finitely-bounded-decidable-prop-ℕ∞↗ x n)
```

### Finite bounds on increasing binary sequences

```agda
finite-bound-ℕ∞↗ : ℕ∞↗ → UU lzero
finite-bound-ℕ∞↗ x = Σ ℕ (is-finitely-bounded-ℕ∞↗ x)
```

### Least finite bounds on increasing binary sequences

```agda
least-finite-bound-ℕ∞↗ : ℕ∞↗ → UU lzero
least-finite-bound-ℕ∞↗ x =
  Σ (finite-bound-ℕ∞↗ x) (λ n → (m : finite-bound-ℕ∞↗ x) → pr1 n ≤-ℕ pr1 m)

abstract
  all-elements-equal-least-finite-bound-ℕ∞↗ :
    (x : ℕ∞↗) → all-elements-equal (least-finite-bound-ℕ∞↗ x)
  all-elements-equal-least-finite-bound-ℕ∞↗
    (x , X) ((n , p) , H) ((m , q) , K) =
    eq-pair-Σ
      ( eq-pair-Σ
        ( antisymmetric-leq-ℕ n m (H (m , q)) (K (n , p)))
        ( eq-is-prop (is-set-bool (x m) true)))
      ( eq-is-prop (is-prop-Π λ u → is-prop-leq-ℕ m (pr1 u)))

abstract
  is-prop-least-finite-bound-ℕ∞↗ :
    (x : ℕ∞↗) → is-prop (least-finite-bound-ℕ∞↗ x)
  is-prop-least-finite-bound-ℕ∞↗ x =
    is-prop-all-elements-equal (all-elements-equal-least-finite-bound-ℕ∞↗ x)

least-finite-bound-prop-ℕ∞↗ : ℕ∞↗ → Prop lzero
least-finite-bound-prop-ℕ∞↗ x =
  ( least-finite-bound-ℕ∞↗ x , is-prop-least-finite-bound-ℕ∞↗ x)
```

### The predicate on an increasing binary sequence of being a finite element

```agda
is-finite-prop-ℕ∞↗ : ℕ∞↗ → Prop lzero
is-finite-prop-ℕ∞↗ = is-inhabited-Prop ∘ finite-bound-ℕ∞↗

is-finite-ℕ∞↗ : ℕ∞↗ → UU lzero
is-finite-ℕ∞↗ = type-Prop ∘ is-finite-prop-ℕ∞↗

is-prop-is-finite-ℕ∞↗ :
  (x : ℕ∞↗) → is-prop (is-finite-ℕ∞↗ x)
is-prop-is-finite-ℕ∞↗ = is-prop-type-Prop ∘ is-finite-prop-ℕ∞↗
```

### The type of finite elements

```agda
Finite-ℕ∞↗ : UU lzero
Finite-ℕ∞↗ = Σ ℕ∞↗ is-finite-ℕ∞↗
```

## Properties

### Infinity is not finitely bounded

```agda
is-not-finitely-bounded-infinity-ℕ∞↗ :
  (n : ℕ) → ¬ (is-finitely-bounded-ℕ∞↗ infinity-ℕ∞↗ n)
is-not-finitely-bounded-infinity-ℕ∞↗ n ()
```

### If an increasing binary sequence is not finitely bounded then it is infinite

```agda
module _
  (x : ℕ∞↗) (H : (n : ℕ) → ¬ (is-finitely-bounded-ℕ∞↗ x n))
  where

  Eq-infinity-is-not-finitely-bounded-ℕ∞↗ : sequence-ℕ∞↗ x ~ const ℕ false
  Eq-infinity-is-not-finitely-bounded-ℕ∞↗ n =
    is-false-is-not-true (sequence-ℕ∞↗ x n) (H n)

  eq-infinity-is-not-finitely-bounded-ℕ∞↗ : x ＝ infinity-ℕ∞↗
  eq-infinity-is-not-finitely-bounded-ℕ∞↗ =
    eq-Eq-ℕ∞↗ (Eq-infinity-is-not-finitely-bounded-ℕ∞↗)
```

### If an increasing binary sequence has an upper bound there exists a unique least upper bound

> This remains to be formalized.

### If an increasing binary sequence is bounded above by a finite number, then it is bounded above by any larger finite number

```agda
abstract
  is-finitely-bounded-succ-is-finitely-bounded-ℕ∞↗ :
    (x : ℕ∞↗) (n : ℕ) →
    is-finitely-bounded-ℕ∞↗ x n → is-finitely-bounded-ℕ∞↗ x (succ-ℕ n)
  is-finitely-bounded-succ-is-finitely-bounded-ℕ∞↗ x n =
    is-true-is-true-leq-bool (is-increasing-sequence-ℕ∞↗ x n)

abstract
  is-finitely-bounded-is-finitely-bounded-by-zero-ℕ∞↗ :
    (x : ℕ∞↗) (n : ℕ) →
    is-finitely-bounded-ℕ∞↗ x 0 → is-finitely-bounded-ℕ∞↗ x n
  is-finitely-bounded-is-finitely-bounded-by-zero-ℕ∞↗ x 0 s = s
  is-finitely-bounded-is-finitely-bounded-by-zero-ℕ∞↗ x (succ-ℕ i) s =
    contrapositive-is-false-bool
      ( is-false-is-false-leq-bool (is-increasing-sequence-ℕ∞↗ x i))
      ( is-finitely-bounded-is-finitely-bounded-by-zero-ℕ∞↗ x i s)

abstract
  is-finitely-bounded-leq-ℕ∞↗ :
    (x : ℕ∞↗) (n m : ℕ) → leq-ℕ n m →
    is-finitely-bounded-ℕ∞↗ x n → is-finitely-bounded-ℕ∞↗ x m
  is-finitely-bounded-leq-ℕ∞↗ x 0 m p =
    is-finitely-bounded-is-finitely-bounded-by-zero-ℕ∞↗ x m
  is-finitely-bounded-leq-ℕ∞↗ x (succ-ℕ n) (succ-ℕ m) =
    is-finitely-bounded-leq-ℕ∞↗ (shift-left-ℕ∞↗ x) n m
```
