# Monotonic endomaps of natural numbers

```agda
module elementary-number-theory.monotonic-endomaps-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Monotic endompas of natural numbers are functions `f : ℕ → ℕ` that preserves or
inverse (strict) inequality of natural numbers.

## Definition

### Increasing endomaps of natural numbers

```agda
module _
  (f : ℕ → ℕ)
  where

  is-increasing-endomap-prop-ℕ : Prop lzero
  is-increasing-endomap-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f i) (f j))))

  is-increasing-endomap-ℕ : UU lzero
  is-increasing-endomap-ℕ =
    type-Prop is-increasing-endomap-prop-ℕ

  is-prop-is-increasing-endomap-ℕ :
    is-prop is-increasing-endomap-ℕ
  is-prop-is-increasing-endomap-ℕ =
    is-prop-type-Prop is-increasing-endomap-prop-ℕ
```

### Strictly increasing endomaps of natural numbers

```agda
module _
  (f : ℕ → ℕ)
  where

  is-strictly-increasing-endomap-prop-ℕ : Prop lzero
  is-strictly-increasing-endomap-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f i) (f j))))

  is-strictly-increasing-endomap-ℕ : UU lzero
  is-strictly-increasing-endomap-ℕ =
    type-Prop is-strictly-increasing-endomap-prop-ℕ

  is-prop-is-strictly-increasing-endomap-ℕ :
    is-prop is-strictly-increasing-endomap-ℕ
  is-prop-is-strictly-increasing-endomap-ℕ =
    is-prop-type-Prop is-strictly-increasing-endomap-prop-ℕ
```

### Decreasing endomaps of natural numbers

```agda
module _
  (f : ℕ → ℕ)
  where

  is-decreasing-endomap-prop-ℕ : Prop lzero
  is-decreasing-endomap-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f j) (f i))))

  is-decreasing-endomap-ℕ : UU lzero
  is-decreasing-endomap-ℕ = type-Prop is-decreasing-endomap-prop-ℕ

  is-prop-is-decreasing-endomap-ℕ : is-prop is-decreasing-endomap-ℕ
  is-prop-is-decreasing-endomap-ℕ =
    is-prop-type-Prop is-decreasing-endomap-prop-ℕ
```

### Stritcly decreasing endomaps of natural numbers

```agda
module _
  (f : ℕ → ℕ)
  where

  is-strictly-decreasing-endomap-prop-ℕ : Prop lzero
  is-strictly-decreasing-endomap-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f j) (f i))))

  is-strictly-decreasing-endomap-ℕ : UU lzero
  is-strictly-decreasing-endomap-ℕ =
    type-Prop is-strictly-decreasing-endomap-prop-ℕ

  is-prop-is-strictly-decreasing-endomap-ℕ :
    is-prop is-strictly-decreasing-endomap-ℕ
  is-prop-is-strictly-decreasing-endomap-ℕ =
    is-prop-type-Prop is-strictly-decreasing-endomap-prop-ℕ
```

## Properties

### There exist no strictly decreasing endomaps of natural numbers

```agda
no-strictly-decreasing-endomap-leq-ℕ :
  (f : ℕ → ℕ) →
  (N : ℕ) →
  is-strictly-decreasing-endomap-ℕ f →
  leq-ℕ (f zero-ℕ) N →
  empty
no-strictly-decreasing-endomap-leq-ℕ f zero-ℕ H =
  concatenate-le-leq-ℕ
    { f 1}
    { f 0}
    { 0}
    ( H 0 1 (succ-le-ℕ 0))
no-strictly-decreasing-endomap-leq-ℕ f (succ-ℕ N) H K =
  no-strictly-decreasing-endomap-leq-ℕ
    ( f ∘ succ-ℕ)
    ( N)
    ( λ i j → H (succ-ℕ i) (succ-ℕ j))
    ( leq-le-succ-ℕ
      ( f 1)
      ( N)
      ( concatenate-le-leq-ℕ
        { f 1}
        { f 0}
        { succ-ℕ N}
        ( H 0 1 (succ-le-ℕ 0))
        ( K)))

no-strictly-decreasing-endomap-ℕ :
  (f : ℕ → ℕ) → ¬ (is-strictly-decreasing-endomap-ℕ f)
no-strictly-decreasing-endomap-ℕ f H =
  no-strictly-decreasing-endomap-leq-ℕ f (f 0) H (refl-leq-ℕ (f 0))
```

### Strictly increasing endomaps of natural numbers are unbounded

```agda
module _
  (f : ℕ → ℕ) (H : is-strictly-increasing-endomap-ℕ f)
  where

  is-unbounded-is-strictly-increasing-endomap-ℕ :
    (M : ℕ) → Σ ℕ (λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ M (f p))
  is-unbounded-is-strictly-increasing-endomap-ℕ zero-ℕ =
    ( zero-ℕ , λ p K → leq-zero-ℕ (f p))
  is-unbounded-is-strictly-increasing-endomap-ℕ (succ-ℕ M) =
    map-Σ
      ( λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ (succ-ℕ M) (f p))
      ( succ-ℕ)
      ( λ N K p I →
        leq-succ-le-ℕ M (f p)
          ( concatenate-leq-le-ℕ
            { M}
            { f N}
            { f p}
            ( K N (refl-leq-ℕ N))
            ( H N p
              ( concatenate-le-leq-ℕ
                { N}
                { succ-ℕ N}
                { p}
                ( succ-le-ℕ N)
                ( I)))))
      ( is-unbounded-is-strictly-increasing-endomap-ℕ M)

  modulus-is-unbounded-is-strictly-increasing-endomap-ℕ : ℕ → ℕ
  modulus-is-unbounded-is-strictly-increasing-endomap-ℕ M =
    pr1 (is-unbounded-is-strictly-increasing-endomap-ℕ M)

  leq-bound-is-strictly-increasing-endomap-ℕ :
    (M : ℕ) →
    (p : ℕ) →
    leq-ℕ (modulus-is-unbounded-is-strictly-increasing-endomap-ℕ M) p →
    leq-ℕ M (f p)
  leq-bound-is-strictly-increasing-endomap-ℕ M =
    pr2 (is-unbounded-is-strictly-increasing-endomap-ℕ M)
```
