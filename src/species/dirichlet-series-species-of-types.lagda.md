# Dirichlet series of species of types

```agda
module species.dirichlet-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

In classical mathematics, the _Dirichlet series_ of a
[species of finite inhabited types](species.of-finite-inhabited-types.md) `T` is
the formal series in `s`:

```text
  Σ (n : ℕ∖{0}), (|T({1,...,n})| n^(-s) / n!).
```

If `s` is a [negative integer](elementary-number-theory.negative-integers.md),
the categorified version of this formula is

```text
  Σ (F : Finite-Type∖{∅}), T(F) × (S → F).
```

We can generalize it to [species of types](species.species-of-types.md) as

```text
  Σ (X : UU), (T(X) × (S → X)).
```

The interesting case is when `s` is a positive number. The categorified version
of this formula then becomes

```text
  Σ ( n : ℕ∖{0}),
    ( Σ ( F : Type-With-Cardinality-ℕ n),
        ( T(F) × (S → cycle-prime-decomposition-ℕ n)).
```

We can generalize the two notions to
[species of types](species.species-of-types.md). Let `H : UU → UU` be a species
such that for every `X , Y : P` the following
[equivalence](foundation-core.equivalences.md) is satisfied
`H (X × Y) ≃ H X × H Y`. Then we can define the
{{#concept "`H`-Dirichlet series" Disambiguation="of species of types" Agda=dirichlet-series-species-types}}
of any species of types `T` by

```text
  Σ (X : P), (T(X) × (S → H(X))).
```

The condition on `H` ensure that all the usual properties of the Dirichlet
series are satisfied.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (H : species-types l1 l2)
  (C1 : preserves-product-species-types H)
  (T : species-types l1 l3)
  (S : UU l4)
  where

  dirichlet-series-species-types : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  dirichlet-series-species-types = Σ (UU l1) (λ X → (T X) × (S → H (X)))
```
