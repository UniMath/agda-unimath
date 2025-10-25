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
{{#concept "finite element" Disambiguation="element of the type of increasing binary sequences" Agda=is-finite-ℕ∞↑}}
if there [exists](foundation.existential-quantification.md) a
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ` such that
`xₙ` is true.

## Definitions

### Finite boundedness of increasing binary sequences

An increasing binary sequence `x` is _bounded_ by a natural number `n` if `x n`
is true.

```agda
is-bounded-decidable-prop-ℕ∞↑ : ℕ∞↑ → ℕ → Decidable-Prop lzero
is-bounded-decidable-prop-ℕ∞↑ x n = is-true-Decidable-Prop (sequence-ℕ∞↑ x n)

is-bounded-prop-ℕ∞↑ : ℕ∞↑ → ℕ → Prop lzero
is-bounded-prop-ℕ∞↑ x n =
  prop-Decidable-Prop (is-bounded-decidable-prop-ℕ∞↑ x n)

is-bounded-ℕ∞↑ : ℕ∞↑ → ℕ → UU lzero
is-bounded-ℕ∞↑ x n = type-Decidable-Prop (is-bounded-decidable-prop-ℕ∞↑ x n)

is-prop-is-bounded-ℕ∞↑ : (x : ℕ∞↑) (n : ℕ) → is-prop (is-bounded-ℕ∞↑ x n)
is-prop-is-bounded-ℕ∞↑ x n =
  is-prop-type-Decidable-Prop (is-bounded-decidable-prop-ℕ∞↑ x n)

is-decidable-is-bounded-ℕ∞↑ :
  (x : ℕ∞↑) (n : ℕ) → is-decidable (is-bounded-ℕ∞↑ x n)
is-decidable-is-bounded-ℕ∞↑ x n =
  is-decidable-Decidable-Prop (is-bounded-decidable-prop-ℕ∞↑ x n)
```

### Bounds on the size of a finite element in increasing binary sequences

```agda
upper-bound-ℕ∞↑ : ℕ∞↑ → UU lzero
upper-bound-ℕ∞↑ x = Σ ℕ (is-bounded-ℕ∞↑ x)
```

### Least upper bounds on the size of a finite element in increasing binary sequences

```agda
least-upper-bound-ℕ∞↑ : ℕ∞↑ → UU lzero
least-upper-bound-ℕ∞↑ x =
  Σ (upper-bound-ℕ∞↑ x) (λ n → (m : upper-bound-ℕ∞↑ x) → pr1 n ≤-ℕ pr1 m)

all-elements-equal-least-upper-bound-ℕ∞↑ :
  (x : ℕ∞↑) → all-elements-equal (least-upper-bound-ℕ∞↑ x)
all-elements-equal-least-upper-bound-ℕ∞↑
  (x , X) ((n , p) , H) ((m , q) , K) =
  eq-pair-Σ
    ( eq-pair-Σ
      ( antisymmetric-leq-ℕ n m (H (m , q)) (K (n , p)))
      ( eq-is-prop (is-set-bool (x m) true)))
    ( eq-is-prop (is-prop-Π λ u → is-prop-leq-ℕ m (pr1 u)))

abstract
  is-prop-least-upper-bound-ℕ∞↑ : (x : ℕ∞↑) → is-prop (least-upper-bound-ℕ∞↑ x)
  is-prop-least-upper-bound-ℕ∞↑ x =
    is-prop-all-elements-equal (all-elements-equal-least-upper-bound-ℕ∞↑ x)

least-upper-bound-prop-ℕ∞↑ : ℕ∞↑ → Prop lzero
least-upper-bound-prop-ℕ∞↑ x =
  ( least-upper-bound-ℕ∞↑ x , is-prop-least-upper-bound-ℕ∞↑ x)
```

### The predicate on an increasing binary sequence of being a finite element

```agda
is-finite-prop-ℕ∞↑ : ℕ∞↑ → Prop lzero
is-finite-prop-ℕ∞↑ = is-inhabited-Prop ∘ upper-bound-ℕ∞↑

is-finite-ℕ∞↑ : ℕ∞↑ → UU lzero
is-finite-ℕ∞↑ = type-Prop ∘ is-finite-prop-ℕ∞↑

is-prop-is-finite-ℕ∞↑ :
  (x : ℕ∞↑) → is-prop (is-finite-ℕ∞↑ x)
is-prop-is-finite-ℕ∞↑ = is-prop-type-Prop ∘ is-finite-prop-ℕ∞↑
```

## Properties

### Infinity is not finitely bounded

```agda
is-not-bounded-infinity-ℕ∞↑ :
  (n : ℕ) → ¬ (is-bounded-ℕ∞↑ infinity-ℕ∞↑ n)
is-not-bounded-infinity-ℕ∞↑ n ()
```

### If an increasing binary sequence is not bounded then it is infinite

```agda
module _
  (x : ℕ∞↑) (H : (n : ℕ) → ¬ (is-bounded-ℕ∞↑ x n))
  where

  Eq-infinity-is-not-bounded-ℕ∞↑ : sequence-ℕ∞↑ x ~ const ℕ false
  Eq-infinity-is-not-bounded-ℕ∞↑ n =
    is-false-is-not-true (sequence-ℕ∞↑ x n) (H n)

  eq-infinity-is-not-bounded-ℕ∞↑ : x ＝ infinity-ℕ∞↑
  eq-infinity-is-not-bounded-ℕ∞↑ =
    eq-Eq-ℕ∞↑ (Eq-infinity-is-not-bounded-ℕ∞↑)
```

### If an increasing binary sequence has an upper bound there exists a unique least upper bound

> This remains to be formalized.

### If an increasing binary sequence is bounded above by a finite number, then it is bounded above by any larger finite number

```agda
abstract
  is-bounded-succ-is-bounded-ℕ∞↑ :
    (x : ℕ∞↑) (n : ℕ) → is-bounded-ℕ∞↑ x n → is-bounded-ℕ∞↑ x (succ-ℕ n)
  is-bounded-succ-is-bounded-ℕ∞↑ x n =
    is-true-is-true-leq-bool (is-increasing-sequence-ℕ∞↑ x n)

abstract
  is-bounded-is-bounded-zero-ℕ∞↑ :
    (x : ℕ∞↑) (n : ℕ) → is-bounded-ℕ∞↑ x 0 → is-bounded-ℕ∞↑ x n
  is-bounded-is-bounded-zero-ℕ∞↑ x 0 s = s
  is-bounded-is-bounded-zero-ℕ∞↑ x (succ-ℕ i) s =
    contrapositive-is-false-bool
      ( is-false-is-false-leq-bool (is-increasing-sequence-ℕ∞↑ x i))
      ( is-bounded-is-bounded-zero-ℕ∞↑ x i s)

abstract
  is-bounded-leq-ℕ∞↑ :
    (x : ℕ∞↑) (n m : ℕ) → leq-ℕ n m → is-bounded-ℕ∞↑ x n → is-bounded-ℕ∞↑ x m
  is-bounded-leq-ℕ∞↑ x 0 m p = is-bounded-is-bounded-zero-ℕ∞↑ x m
  is-bounded-leq-ℕ∞↑ x (succ-ℕ n) (succ-ℕ m) =
    is-bounded-leq-ℕ∞↑ (shift-left-ℕ∞↑ x) n m
```
