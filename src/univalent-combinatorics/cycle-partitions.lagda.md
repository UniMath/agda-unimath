# Cycle partitions of finite types

```agda
module univalent-combinatorics.cycle-partitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.cyclic-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A cycle partition of a finite type `A` is a finite family of cyclic finite types
equipped with an equivalence from `A` to the total space of the underlying types
of the family. The type of cyclic partitions of `A` is equivalent to the type of
permutations of `A`.

## Definition

```agda
cyclic-partition-Finite-Type :
  {l : Level} (l2 l3 : Level) → Finite-Type l → UU (l ⊔ lsuc l2 ⊔ lsuc l3)
cyclic-partition-Finite-Type l2 l3 X =
  Σ ( Finite-Type l2)
    ( λ Y →
      Σ ( type-Finite-Type Y → Σ ℕ (λ n → Cyclic-Type l3 (succ-ℕ n)))
        ( λ C →
          type-Finite-Type X ≃
          Σ ( type-Finite-Type Y)
            ( λ y → type-Cyclic-Type (succ-ℕ (pr1 (C y))) (pr2 (C y)))))

module _
  {l1 l2 l3 : Level} (X : Finite-Type l1)
  (C : cyclic-partition-Finite-Type l2 l3 X)
  where

  finite-indexing-type-cyclic-partition-Finite-Type : Finite-Type l2
  finite-indexing-type-cyclic-partition-Finite-Type = pr1 C

  indexing-type-cyclic-partition-Finite-Type : UU l2
  indexing-type-cyclic-partition-Finite-Type =
    type-Finite-Type finite-indexing-type-cyclic-partition-Finite-Type

  order-cycle-cyclic-partition-Finite-Type :
    indexing-type-cyclic-partition-Finite-Type → ℕ
  order-cycle-cyclic-partition-Finite-Type y = succ-ℕ (pr1 (pr1 (pr2 C) y))

  cycle-cyclic-partition-Finite-Type :
    (y : indexing-type-cyclic-partition-Finite-Type) →
    Cyclic-Type l3 (order-cycle-cyclic-partition-Finite-Type y)
  cycle-cyclic-partition-Finite-Type y =
    pr2 (pr1 (pr2 C) y)

  type-cycle-cyclic-partition-Finite-Type :
    indexing-type-cyclic-partition-Finite-Type → UU l3
  type-cycle-cyclic-partition-Finite-Type y =
    type-Cyclic-Type
      ( order-cycle-cyclic-partition-Finite-Type y)
      ( cycle-cyclic-partition-Finite-Type y)

  equiv-cyclic-partition-Finite-Type :
    type-Finite-Type X ≃
    Σ indexing-type-cyclic-partition-Finite-Type
      type-cycle-cyclic-partition-Finite-Type
  equiv-cyclic-partition-Finite-Type = pr2 (pr2 C)
```
