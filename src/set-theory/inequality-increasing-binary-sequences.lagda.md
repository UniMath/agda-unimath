# Inequality of increasing binary sequences

```agda
module set-theory.inequality-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.posets
open import order-theory.preorders

open import set-theory.increasing-binary-sequences
```

</details>

## Idea

Given two
[increasing binary sequences](set-theory.inequality-increasing-binary-sequences.md)
`x` and `y`, then `x` is _less than or equal_ to `y` if `yᵢ ≤ xᵢ` for every
`i : ℕ`. This defines the
{{#concept "standard inequality" Disambiguation="on increasing binary sequences" Agda=leq-ℕ∞↗}}
relation on increasing binary sequences.

## Definitions

```agda
leq-ℕ∞↗ : ℕ∞↗ → ℕ∞↗ → UU lzero
leq-ℕ∞↗ x y = (n : ℕ) → leq-bool (sequence-ℕ∞↗ y n) (sequence-ℕ∞↗ x n)

infix 30 _≤-ℕ∞↗_
_≤-ℕ∞↗_ : ℕ∞↗ → ℕ∞↗ → UU lzero
_≤-ℕ∞↗_ = leq-ℕ∞↗

abstract
  is-prop-leq-ℕ∞↗ : (x y : ℕ∞↗) → is-prop (leq-ℕ∞↗ x y)
  is-prop-leq-ℕ∞↗ x y =
    is-prop-Π (λ n → is-prop-leq-bool {sequence-ℕ∞↗ y n} {sequence-ℕ∞↗ x n})

leq-prop-ℕ∞↗ : ℕ∞↗ → ℕ∞↗ → Prop lzero
leq-prop-ℕ∞↗ x y = (leq-ℕ∞↗ x y , is-prop-leq-ℕ∞↗ x y)
```

## Properties

### Inequality of increasing binary sequences is reflexive

```agda
abstract
  refl-leq-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ x x
  refl-leq-ℕ∞↗ x n = refl-leq-bool {sequence-ℕ∞↗ x n}

abstract
  leq-Eq-ℕ∞↗' : (x y : ℕ∞↗) → Eq-ℕ∞↗ y x → leq-ℕ∞↗ x y
  leq-Eq-ℕ∞↗' x y H = leq-eq-bool ∘ H

abstract
  leq-Eq-ℕ∞↗ : (x y : ℕ∞↗) → Eq-ℕ∞↗ x y → leq-ℕ∞↗ x y
  leq-Eq-ℕ∞↗ x y H = leq-Eq-ℕ∞↗' x y (inv-htpy H)

abstract
  leq-eq-ℕ∞↗ : (x y : ℕ∞↗) → x ＝ y → leq-ℕ∞↗ x y
  leq-eq-ℕ∞↗ x .x refl = refl-leq-ℕ∞↗ x
```

### Inequality of increasing binary sequences is transitive

```agda
transitive-leq-ℕ∞↗ :
  (x y z : ℕ∞↗) → leq-ℕ∞↗ y z → leq-ℕ∞↗ x y → leq-ℕ∞↗ x z
transitive-leq-ℕ∞↗ x y z p q n =
  transitive-leq-bool
    { sequence-ℕ∞↗ z n}
    { sequence-ℕ∞↗ y n}
    { sequence-ℕ∞↗ x n}
    ( q n)
    ( p n)
```

### Inequality of increasing binary sequences is antisymmetric

```agda
abstract
  antisymmetric-leq-ℕ∞↗ :
    (x y : ℕ∞↗) → leq-ℕ∞↗ x y → leq-ℕ∞↗ y x → x ＝ y
  antisymmetric-leq-ℕ∞↗ x y p q =
    eq-Eq-ℕ∞↗
      ( λ n →
        antisymmetric-leq-bool
          { sequence-ℕ∞↗ x n}
          { sequence-ℕ∞↗ y n}
          ( q n)
          ( p n))
```

### The poset of increasing binary sequences

```agda
is-preorder-leq-ℕ∞↗ :
  is-preorder-Relation-Prop leq-prop-ℕ∞↗
is-preorder-leq-ℕ∞↗ = (refl-leq-ℕ∞↗ , transitive-leq-ℕ∞↗)

ℕ∞↗-Preorder : Preorder lzero lzero
ℕ∞↗-Preorder = (ℕ∞↗ , leq-prop-ℕ∞↗ , is-preorder-leq-ℕ∞↗)

ℕ∞↗-Poset : Poset lzero lzero
ℕ∞↗-Poset = (ℕ∞↗-Preorder , antisymmetric-leq-ℕ∞↗)
```

### The successor function preserves order

```agda
preserves-order-succ-ℕ∞↗ :
  (x y : ℕ∞↗) → leq-ℕ∞↗ x y → leq-ℕ∞↗ (succ-ℕ∞↗ x) (succ-ℕ∞↗ y)
preserves-order-succ-ℕ∞↗ x y p zero-ℕ = star
preserves-order-succ-ℕ∞↗ x y p (succ-ℕ n) = p n
```

### The successor function is inflationary

```agda
leq-succ-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ x (succ-ℕ∞↗ x)
leq-succ-ℕ∞↗ x zero-ℕ = star
leq-succ-ℕ∞↗ x (succ-ℕ n) = is-increasing-sequence-ℕ∞↗ x n
```

### Zero is the smallest element

```agda
leq-zero-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ zero-ℕ∞↗ x
leq-zero-ℕ∞↗ x n = leq-true-bool {sequence-ℕ∞↗ x n}

Eq-leq-zero-ℕ∞↗ :
  (x : ℕ∞↗) → leq-ℕ∞↗ x zero-ℕ∞↗ → Eq-ℕ∞↗ x zero-ℕ∞↗
Eq-leq-zero-ℕ∞↗ x p = eq-leq-true-bool ∘ p

eq-leq-zero-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ x zero-ℕ∞↗ → x ＝ zero-ℕ∞↗
eq-leq-zero-ℕ∞↗ x p = eq-Eq-ℕ∞↗ (Eq-leq-zero-ℕ∞↗ x p)
```

### Infinity is the largest element

```agda
infinity-leq-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ x infinity-ℕ∞↗
infinity-leq-ℕ∞↗ x n = leq-false-bool {sequence-ℕ∞↗ x n}

Eq-leq-infinity-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ infinity-ℕ∞↗ x → Eq-ℕ∞↗ x infinity-ℕ∞↗
Eq-leq-infinity-ℕ∞↗ x p = eq-leq-false-bool ∘ p

eq-leq-infinity-ℕ∞↗ : (x : ℕ∞↗) → leq-ℕ∞↗ infinity-ℕ∞↗ x → x ＝ infinity-ℕ∞↗
eq-leq-infinity-ℕ∞↗ x p = eq-Eq-ℕ∞↗ (Eq-leq-infinity-ℕ∞↗ x p)
```
