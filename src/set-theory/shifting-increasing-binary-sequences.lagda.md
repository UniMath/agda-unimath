# Shifting increasing binary sequences

```agda
module set-theory.shifting-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.function-types
open import foundation.homotopies
open import foundation.iterating-functions

open import foundation-core.identity-types

open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

For each [natural number](elementary-number-theory.natural-numbers) `n`, we
define a
{{#concept "shift operation" Disambiguation="on increasing binary sequences by a natural number" Agda=shift-ℕ∞↗}}
on [increasing binary sequences](set-theory.increasing-binary-sequences.md) by
the `n` times [iterated](foundation.iterating-functions.md) successor function.

## Definition

```agda
shift-ℕ∞↗ : ℕ → ℕ∞↗ → ℕ∞↗
shift-ℕ∞↗ n = iterate n succ-ℕ∞↗
```

## Properties

### Computing the shift operation at a successor

```agda
abstract
  compute-shift-succ-ℕ∞↗ :
    (n : ℕ) → shift-ℕ∞↗ (succ-ℕ n) ~ shift-ℕ∞↗ n ∘ succ-ℕ∞↗
  compute-shift-succ-ℕ∞↗ n =
    reassociate-iterate-succ-ℕ n succ-ℕ∞↗
```

### The `n + m`'th position of `shift m x` is `x n`

```agda
compute-ev-add-shift-ℕ∞↗ :
  (n m : ℕ) (x : ℕ∞↗) → ev-ℕ∞↗ (add-ℕ n m) (shift-ℕ∞↗ m x) ＝ ev-ℕ∞↗ n x
compute-ev-add-shift-ℕ∞↗ n zero-ℕ x = refl
compute-ev-add-shift-ℕ∞↗ n (succ-ℕ m) x = compute-ev-add-shift-ℕ∞↗ n m x

compute-ev-add'-shift-ℕ∞↗ :
  (n m : ℕ) (x : ℕ∞↗) → ev-ℕ∞↗ (add-ℕ' n m) (shift-ℕ∞↗ m x) ＝ ev-ℕ∞↗ n x
compute-ev-add'-shift-ℕ∞↗ n m x =
  ( ap (λ - → ev-ℕ∞↗ - (shift-ℕ∞↗ m x)) (commutative-add-ℕ m n)) ∙
  ( compute-ev-add-shift-ℕ∞↗ n m x)
```

### The `n`'th position of `shift n x` is `x 0`

```agda
compute-ev-shift-ℕ∞↗ :
  (n : ℕ) (x : ℕ∞↗) → ev-ℕ∞↗ n (shift-ℕ∞↗ n x) ＝ ev-ℕ∞↗ 0 x
compute-ev-shift-ℕ∞↗ n x = compute-ev-add'-shift-ℕ∞↗ 0 n x
```

### The `n`'th position of `shift (n+1) x` is `false`

```agda
compute-ev-shift-succ-ℕ∞↗ :
  (n : ℕ) (x : ℕ∞↗) → ev-ℕ∞↗ n (shift-ℕ∞↗ (succ-ℕ n) x) ＝ false
compute-ev-shift-succ-ℕ∞↗ zero-ℕ x = refl
compute-ev-shift-succ-ℕ∞↗ (succ-ℕ n) x = compute-ev-shift-succ-ℕ∞↗ n x
```

### Computing the shift operation at finite elements

```agda
abstract
  compute-shift-add'-increasing-binary-sequence-ℕ :
    (n m : ℕ) →
    shift-ℕ∞↗ n (increasing-binary-sequence-ℕ m) ＝
    increasing-binary-sequence-ℕ (add-ℕ' n m)
  compute-shift-add'-increasing-binary-sequence-ℕ zero-ℕ m = refl
  compute-shift-add'-increasing-binary-sequence-ℕ (succ-ℕ n) m =
    ap succ-ℕ∞↗ (compute-shift-add'-increasing-binary-sequence-ℕ n m)

abstract
  compute-shift-add-increasing-binary-sequence-ℕ :
    (n m : ℕ) →
    shift-ℕ∞↗ n (increasing-binary-sequence-ℕ m) ＝
    increasing-binary-sequence-ℕ (add-ℕ n m)
  compute-shift-add-increasing-binary-sequence-ℕ n m =
    ( compute-shift-add'-increasing-binary-sequence-ℕ n m) ∙
    ( ap increasing-binary-sequence-ℕ (commutative-add-ℕ m n))
```

### Computing the shift operation at zero

```agda
abstract
  compute-shift-zero-ℕ∞↗ :
    (n : ℕ) → shift-ℕ∞↗ n zero-ℕ∞↗ ＝ increasing-binary-sequence-ℕ n
  compute-shift-zero-ℕ∞↗ n = compute-shift-add-increasing-binary-sequence-ℕ n 0

  inv-compute-shift-zero-ℕ∞↗ :
    (n : ℕ) → increasing-binary-sequence-ℕ n ＝ shift-ℕ∞↗ n zero-ℕ∞↗
  inv-compute-shift-zero-ℕ∞↗ n = inv (compute-shift-zero-ℕ∞↗ n)
```

### Computing the shift operation at infinity

```agda
abstract
  compute-shift-infinity-ℕ∞↗ :
    (n : ℕ) → shift-ℕ∞↗ n infinity-ℕ∞↗ ＝ infinity-ℕ∞↗
  compute-shift-infinity-ℕ∞↗ zero-ℕ = refl
  compute-shift-infinity-ℕ∞↗ (succ-ℕ n) =
    ap succ-ℕ∞↗ (compute-shift-infinity-ℕ∞↗ n) ∙ succ-infinity-ℕ∞↗

  inv-compute-shift-infinity-ℕ∞↗ :
    (n : ℕ) → infinity-ℕ∞↗ ＝ shift-ℕ∞↗ n infinity-ℕ∞↗
  inv-compute-shift-infinity-ℕ∞↗ n = inv (compute-shift-infinity-ℕ∞↗ n)
```
