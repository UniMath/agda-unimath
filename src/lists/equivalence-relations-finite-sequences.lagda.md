# Equivalence relations on finite sequences

```agda
module lists.equivalence-relations-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.dependent-products-equivalence-relations
open import foundation.equivalence-relations
open import foundation.universe-levels

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An [equivalence relation](foundation.equivalence-relations.md) `R` on a type `A`
induces an equivalence relation on [finite sequences](lists.finite-sequences.md)
of length `n` in `A`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : equivalence-relation l2 A)
  (n : ℕ)
  where

  equivalence-relation-fin-sequence-equivalence-relation :
    equivalence-relation l2 (fin-sequence A n)
  equivalence-relation-fin-sequence-equivalence-relation =
    Π-equivalence-relation (Fin n) (λ _ → R)

  sim-fin-sequence-equivalence-relation : Relation l2 (fin-sequence A n)
  sim-fin-sequence-equivalence-relation =
    sim-equivalence-relation
      ( equivalence-relation-fin-sequence-equivalence-relation)

  sim-prop-fin-sequence-equivalence-relation :
    Relation-Prop l2 (fin-sequence A n)
  sim-prop-fin-sequence-equivalence-relation =
    prop-equivalence-relation
      ( equivalence-relation-fin-sequence-equivalence-relation)
```
