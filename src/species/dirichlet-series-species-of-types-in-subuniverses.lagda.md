# Dirichlet series of species of types in subuniverses

```agda
module species.dirichlet-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses
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

We can generalize the two notions to species of types in subuniverses. Let `P`
and `Q` two subuniverse such that `P` is closed by cartesian product. Let
`H : P → UU` be a species such that for every `X , Y : P` the following equality
is satisfied `H (X × Y) ≃ H X × H Y`. Then we can define the `H`-Dirichlet
series to any species of subuniverse `T` by

```text
Σ (X : P) (T (X) × (S → H (X)))
```

The condition on `H` ensure that all the usual properties of the Dirichlet
series are satisfied.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (C1 : is-closed-under-products-subuniverse P)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (T : species-subuniverse P Q)
  (S : UU l6)
  where

  dirichlet-series-species-subuniverse : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l5 ⊔ l6)
  dirichlet-series-species-subuniverse =
    Σ (type-subuniverse P) (λ X → inclusion-subuniverse Q (T X) × (S → H (X)))
```
