# The pronic numbers

```agda
module elementary-number-theory.pronic-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.dependent-pair-types
open import foundation.coproduct-types
open import foundation.identity-types
```

</details>

## Idea

The {{#concept "pronic numbers" Agda=pronic-number-ℕ WD="pronic number" WDID=Q1486643}} are the [natural numbers](elementary-number-theory.natural-numbers.md)
of the form

$$
  n(n+1).
$$

The sequence `0, 2, 6, 12, 20, 30, 42, ⋯` of pronic numbers is listed as
[A002378](https://oeis.org/A002378) in the OEIS {{#cite "OEIS"}}. The $n$th
pronic number is [even](elementary-number-theory.parity-natural-numbers.md) for
every $n$, and it is twice the $n$th
[triangular number](elementary-number-theory.triangular-numbers.md).

## Definitions

### The pronic numbers

```agda
pronic-number-ℕ : ℕ → ℕ
pronic-number-ℕ n = n *ℕ succ-ℕ n
```

## Properties

### The $n$th pronic number $n(n + 1)$ is even

```agda
abstract
  is-even-pronic-number-ℕ :
    (n : ℕ) → is-even-ℕ (pronic-number-ℕ n)
  is-even-pronic-number-ℕ n
    with is-even-or-is-even-succ-ℕ n
  ... | inl H =
    is-even-div-is-even-ℕ
      ( pronic-number-ℕ n)
      ( n)
      ( H)
      ( succ-ℕ n , commutative-mul-ℕ (succ-ℕ n) n)
  ... | inr H =
    is-even-div-is-even-ℕ
      ( pronic-number-ℕ n)
      ( succ-ℕ n)
      ( H)
      ( n , refl)
```

### The $(n+1)$st pronic number

We have `(n + 1) * (n + 2) ＝ n * (n + 1) + 2 * (n + 1)`

```agda
compute-pronic-number-succ-ℕ :
  (n : ℕ) → pronic-number-ℕ (succ-ℕ n) ＝ pronic-number-ℕ n +ℕ 2 *ℕ succ-ℕ n
compute-pronic-number-succ-ℕ n =
  commutative-mul-ℕ (succ-ℕ n) (succ-ℕ (succ-ℕ n)) ∙
  right-distributive-mul-add-ℕ n 2 (succ-ℕ n)
```

## See also

- [Nicomachus's Theorem](elementary-number-theory.nicomachuss-theorem.md)
- [Square pyramidal numbers](elementary-number-theory.square-pyramidal-numbers.md)
- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
- [Triangular numbers](elementary-number-theory.triangular-numbers.md)
