# Dirichlet series of species of finite inhabited types

```agda
module species.dirichlet-series-species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-finite-inhabited-types

open import univalent-combinatorics.cycle-prime-decomposition-natural-numbers
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

In classical mathematics, the _Dirichlet series_ of a
[species of finite inhabited types](species.species-of-finite-inhabited-types.md)
`T` is the formal series in `s`:

```text
  Σ (n : ℕ∖{0}) (|T({1,...,n})| n^(-s) / n!).
```

If `s` is a [negative integer](elementary-number-theory.negative-integers.md),
the categorified version of this formula is

```text
  Σ (F : Finite-Type∖{∅}), T(F) × (S → F).
```

We can generalize it to [species of types](species.species-of-types.md) as

```text
  Σ (X : UU) (T(X) × (S → X)).
```

The interesting case is when `s` is a positive number. The categorified version
of this formula then becomes

```text
  Σ ( n : ℕ∖{0}),
    ( Σ ( F : Type-With-Cardinality-ℕ n) ,
        ( T(F) × (S → cycle-prime-decomposition-ℕ n)).
```

We have picked the [concrete group](group-theory.concrete-groups.md)
`cycle-prime-decomposition-ℕ n` because it is closed under cartesian product and
also because its groupoid cardinality is `1/n`.

## Definition

```agda
dirichlet-series-species-Inhabited-Finite-Type :
  {l1 l2 l3 : Level} → species-Inhabited-Finite-Type l1 l2 → UU l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
dirichlet-series-species-Inhabited-Finite-Type {l1} T S =
  Σ ( ℕ)
    ( λ n →
      Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ n))
        ( λ F →
          ( type-Finite-Type
            ( T
              ( type-Type-With-Cardinality-ℕ (succ-ℕ n) F ,
                is-finite-and-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ
                  n
                  F))) ×
          ( S → cycle-prime-decomposition-ℕ (succ-ℕ n) _)))
```
