# Taxicab numbers

```agda
module elementary-number-theory.taxicab-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.cubes-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The `n`-th
{{#concept "taxicab number" Agda=is-taxicab-number-ℕ WD="taxicab number" WDID=Q1462591}}
`taxicab n` is the smallest
[natural number](elementary-number-theory.natural-numbers.md) `x` such that `x`
is a [sum](elementary-number-theory.addition-natural-numbers.md) of two
[cubes](elementary-number-theory.cubes-natural-numbers.md) in `n`
[distinct](foundation.negated-equality.md) ways.

**Note:** The definition of taxicab numbers only considers sums of
[positive integers](elementary-number-theory.nonzero-natural-numbers.md). Note
that if `n` is a cube, i.e., if `n ＝ c³`, then the only solutions to the
equation

```text
  a³ + b³ = c³
```

have either `a ＝ 0` or `b ＝ 0` by
[Fermat's last theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem).
Therefore `n` can be written in at least two different ways as a sum of cubes of
positive natural numbers if and only if it can be written in at least two
different ways as a sum of cubes of arbitrary natural numbers. However, the
class of natural numbers that can be written in exactly one way as a sum of
cubes is different when we consider sums of cubes of positive natural numbers or
sums of cubes of arbitrary natural numbers.

## Definitions

### The type of decompositions of a natural number as a sum of cubes

```agda
sum-of-cubes-decomposition-ℕ : ℕ → UU lzero
sum-of-cubes-decomposition-ℕ x =
  Σ ( nonzero-ℕ)
    ( λ y →
      Σ ( nonzero-ℕ)
        ( λ z →
          ( leq-ℕ (nat-nonzero-ℕ y) (nat-nonzero-ℕ z)) ×
          ( cube-ℕ (nat-nonzero-ℕ y) +ℕ cube-ℕ (nat-nonzero-ℕ z) ＝ x)))
```

### The predicate of being a sum of two cubes in exactly `n` distinct ways

A number `x` is a sum of cubes in `n` distinct ways if there is an equivalence

```text
  Fin n ≃ sum-of-cubes-decomposition-ℕ x
```

from the
[standard finite type](univalent-combinatorics.standard-finite-types.md) to the
type `sum-of-cubes-decomposition-ℕ x` of ways of writing `x` as a sum of cubes.

```agda
is-sum-of-cubes-in-number-of-distinct-ways-ℕ : ℕ → ℕ → UU lzero
is-sum-of-cubes-in-number-of-distinct-ways-ℕ n x =
  Fin n ≃ sum-of-cubes-decomposition-ℕ x
```

### The predicate of being the `n`-th taxicab number

```agda
is-taxicab-number-ℕ : ℕ → ℕ → UU lzero
is-taxicab-number-ℕ n x =
  is-sum-of-cubes-in-number-of-distinct-ways-ℕ n x ×
  ((y : ℕ) → is-sum-of-cubes-in-number-of-distinct-ways-ℕ n y → leq-ℕ x y)
```

## See also

- [The Hardy-Ramanujan number](elementary-number-theory.hardy-ramanujan-number.md)

## External links

- [Taxicab numbers](https://en.wikipedia.org/wiki/Taxicab_number) at Wikipedia
- [Taxicab numbers](https://oeis.org/A011541) in the OEIS.
