# The Bell numbers

```agda
module elementary-number-theory.bell-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers
```

</details>

## Idea

The {{#concept "Bell numbers" Agda=bell-number-ℕ WDID=Q816063 WD="Bell number"}}
[count](univalent-combinatorics.counting.md) the number of ways to
[partition](univalent-combinatorics.partitions.md) a
[set of size](univalent-combinatorics.finite-types.md) $n$. The Bell numbers can
be defined recursively by $B_0 := 1$ and

$$
  B_{n+1} := \sum_{k=0}^{n} \binom{n}{k}B_k.
$$

The Bell numbers are listed as sequence A000110 in the
[OEIS](literature.oeis.md) {{#cite OEIS}}.

## Definitions

### The Bell numbers

```agda
bell-number-ℕ : ℕ → ℕ
bell-number-ℕ =
  strong-rec-ℕ 1
    ( λ n B →
      bounded-sum-ℕ
        ( succ-ℕ n)
        ( λ k H →
          binomial-coefficient-ℕ n k *ℕ B k (leq-le-succ-ℕ k n H)))
```

## References

{{#bibliography}}
