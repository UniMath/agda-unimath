# Sequential diagrams

```agda
module synthetic-homotopy-theory.sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **sequential diagram** `(A, a)` is a [sequence](foundation.sequences.md) of
types `A : ℕ → 𝓤` over the natural numbers, equipped with a family of maps
`aₙ : A n → A (n + 1)` for all `n`.

## Definition

```agda
sequential-diagram : (l : Level) → UU (lsuc l)
sequential-diagram l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A n → A (succ-ℕ n))

module _
  { l : Level} (A : sequential-diagram l)
  where

  family-sequential-diagram : ℕ → UU l
  family-sequential-diagram = pr1 A

  map-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram n → family-sequential-diagram (succ-ℕ n)
  map-sequential-diagram = pr2 A
```

## References

1. Kristina Sojakova, Floris van Doorn, and Egbert Rijke. 2020. Sequential
   Colimits in Homotopy Type Theory. In Proceedings of the 35th Annual ACM/IEEE
   Symposium on Logic in Computer Science (LICS '20). Association for Computing
   Machinery, New York, NY, USA, 845–858,
   [DOI:10.1145](https://doi.org/10.1145/3373718.3394801)
