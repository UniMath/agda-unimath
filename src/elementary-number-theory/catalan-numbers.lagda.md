# Catalan numbers

```agda
module elementary-number-theory.catalan-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "Catalan numbers" WD="Catalan number" WDID=Q270513 OEIS=A000108 Agda=catalan-numbers}}
$C_n$ is a [sequence](lists.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) that occur in
several combinatorics problems. The sequence starts

```text
  n   0   1   2   3   4   5   6
  Cₙ  1   1   2   5  14  42 132 ⋯
```

The Catalan numbers may be defined by any of the formulas

1. $C_{n + 1} = ∑_{k = 0}^n C_k C_{n-k}$, with $C_0 = 1$,
2. $C_n = {2n \choose n} - {2n \choose n + 1}$,
3. $C_{n+1} = \frac{2(2n+1)}{n+2}C_n$, with $C_0 = 1$,
4. $C_{n} = \frac{1}{n+1}{2n \choose n}$,
5. $C_{n} = \frac{(2n)!}{(n+1)!n!}$.

Where $n \choose k$ are
[binomial coefficients](elementary-number-theory.binomial-coefficients.md) and
$n!$ is the [factorial function](elementary-number-theory.factorials.md).

## Definitions

### Inductive sum formula for the Catalan numbers

The Catalan numbers may be defined to be the sequence satisfying $C_0 = 1$ and
the recurrence relation

$$
C_{n + 1} = ∑_{k = 0}^n C_k C_{n-k}.
$$

```agda
catalan-numbers : ℕ → ℕ
catalan-numbers =
  strong-ind-ℕ
    ( λ _ → ℕ)
    ( 1)
    ( λ k C →
      sum-Fin-ℕ k
        ( λ i →
          mul-ℕ
            ( C ( nat-Fin k i)
                ( leq-le-ℕ (nat-Fin k i) k (strict-upper-bound-nat-Fin k i)))
            ( C ( dist-ℕ (nat-Fin k i) k)
                ( leq-dist-ℕ
                  ( nat-Fin k i)
                  ( k)
                  ( leq-le-ℕ
                    ( nat-Fin k i)
                    ( k)
                    ( strict-upper-bound-nat-Fin k i))))))
```

### Binomial difference formula for the Catalan numbers

The Catalan numbers may be computed as a
[distance](elementary-number-theory.distance-natural-numbers.md) between two
consecutive binomial coefficients

$$
C_n = \lvert{2n \choose n} - {2n \choose n + 1}\rvert.
$$

Since ${2n \choose n}$ in general is larger than or equal to
${2n \choose n + 1}$, this distance is equal to the difference

$$
C_n = {2n \choose n} - {2n \choose n + 1}.
$$

However, we prefer the use of the distance binary operation on natural numbers
in general at it is a total function on natural numbers, and allows us to skip
proving this inequality.

```agda
catalan-numbers-binomial : ℕ → ℕ
catalan-numbers-binomial n =
  dist-ℕ
    ( binomial-coefficient-ℕ (2 *ℕ n) n)
    ( binomial-coefficient-ℕ (2 *ℕ n) (succ-ℕ n))
```

## External links

- [Catalan number](https://en.wikipedia.org/wiki/Catalan_number) at Wikipedia
- [Catalan Number](https://mathworld.wolfram.com/CatalanNumber.html) at Wolfram
  MathWorld
- [A000108](https://oeis.org/A000108) in the OEIS
