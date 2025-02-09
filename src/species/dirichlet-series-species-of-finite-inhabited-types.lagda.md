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

In classical mathematics, the Dirichlet series of a species of finite inhabited
types `T` is the formal series in `s` :

```text
Σ (n : ℕ∖{0}) (|T({1,...,n}| n^(-s) / n!))
```

If `s` is a negative integer, the categorified version of this formula is

```text
Σ (F : 𝔽 ∖ {∅}), T (F) × (S → F)
```

We can generalize it to species of types as

```text
Σ (U : UU) (T (U) × (S → U))
```

The interesting case is when `s` is a positive number. The categorified version
of this formula then becomes

```text
Σ ( n : ℕ ∖ {0}),
  ( Σ (F : UU-Fin n) , T (F) × (S → cycle-prime-decomposition-ℕ (n))
```

We have picked the concrete group `cycle-prime-decomposition-ℕ (n)` because it
is closed under cartesian product and also because its groupoid cardinality is
equal to `1/n`.

## Definition

```agda
dirichlet-series-species-Inhabited-Finite-Type :
  {l1 l2 l3 : Level} → species-Inhabited-Finite-Type l1 l2 → UU l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
dirichlet-series-species-Inhabited-Finite-Type {l1} T S =
  Σ ( ℕ)
    ( λ n →
      Σ ( UU-Fin l1 (succ-ℕ n))
        ( λ F →
          type-𝔽
            ( T
              ( type-UU-Fin (succ-ℕ n) F ,
                is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F)) ×
          S → cycle-prime-decomposition-ℕ (succ-ℕ n) _))
```
