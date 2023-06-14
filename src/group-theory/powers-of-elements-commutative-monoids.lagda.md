# Powers of elements in commutative monoids

```agda
module group-theory.powers-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.commutative-monoids
```

</details>

## Idea

Consider an element `x` in a
[commutative monoid](group-theory.commutative-monoids.md) and a
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`. The
`n`-th **power** of `x` is the `n` times iterated product of `x` with itself.

## Definition

```agda
power-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) →
  ℕ → type-Commutative-Monoid M → type-Commutative-Monoid M
power-Commutative-Monoid M zero-ℕ x = unit-Commutative-Monoid M
power-Commutative-Monoid M (succ-ℕ zero-ℕ) x = x
power-Commutative-Monoid M (succ-ℕ (succ-ℕ n)) x =
  mul-Commutative-Monoid M (power-Commutative-Monoid M (succ-ℕ n) x) x
```
