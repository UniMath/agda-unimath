# The binomial coefficients

```agda
module elementary-number-theory.binomial-coefficients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "binomial coefficient" WD="binomial coefficient" WDID=Q209875 Agda=binomial-coefficient-ℕ}}
`(n choose k)` measures
[how many decidable subsets](univalent-combinatorics.counting-decidable-subtypes.md)
of size `k` there are of a
[finite type](univalent-combinatorics.finite-types.md) of size `n`.

## Definition

### Binomial coefficients of natural numbers

```agda
binomial-coefficient-ℕ : ℕ → ℕ → ℕ
binomial-coefficient-ℕ zero-ℕ zero-ℕ = 1
binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) = 0
binomial-coefficient-ℕ (succ-ℕ n) zero-ℕ = 1
binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) =
  (binomial-coefficient-ℕ n k) +ℕ (binomial-coefficient-ℕ n (succ-ℕ k))
```

### Binomial coefficients indexed by elements of standard finite types

```agda
binomial-coefficient-Fin : (n : ℕ) → Fin (succ-ℕ n) → ℕ
binomial-coefficient-Fin n x = binomial-coefficient-ℕ n (nat-Fin (succ-ℕ n) x)
```

## Properties

### If `k > n` then `binomial-coefficient-ℕ n k ＝ 0`

```agda
is-zero-binomial-coefficient-ℕ :
  (n k : ℕ) → le-ℕ n k → is-zero-ℕ (binomial-coefficient-ℕ n k)
is-zero-binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) _ = refl
is-zero-binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) H =
  ap-add-ℕ
    ( is-zero-binomial-coefficient-ℕ n k H)
    ( is-zero-binomial-coefficient-ℕ n (succ-ℕ k) (preserves-le-succ-ℕ n k H))
```

### `binomial-coefficient-ℕ n n ＝ 1`

```agda
is-one-on-diagonal-binomial-coefficient-ℕ :
  (n : ℕ) → is-one-ℕ (binomial-coefficient-ℕ n n)
is-one-on-diagonal-binomial-coefficient-ℕ zero-ℕ = refl
is-one-on-diagonal-binomial-coefficient-ℕ (succ-ℕ n) =
  ap-add-ℕ
    ( is-one-on-diagonal-binomial-coefficient-ℕ n)
    ( is-zero-binomial-coefficient-ℕ n (succ-ℕ n) (succ-le-ℕ n))
```

## See also

- [Binomial types](univalent-combinatorics.binomial-types.md)

## External links

- [Binomial coefficients](https://www.britannica.com/science/binomial-coefficient)
  at Britannica
- [Binomial coefficient](https://en.wikipedia.org/wiki/Binomial_coefficient) at
  Wikipedia
- [Binomial Coefficient](https://mathworld.wolfram.com/BinomialCoefficient.html)
  at Wolfram MathWorld
