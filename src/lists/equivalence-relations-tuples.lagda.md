# Equivalence relations on tuples

```agda
module lists.equivalence-relations-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.binary-relations-tuples
open import lists.tuples
```

</details>

## Idea

An [equivalence relation](foundation.equivalence-relations.md) on a type `A`
induces an equivalence relation on the type of `n`-[tuples](lists.tuples.md) of
`A`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : equivalence-relation l2 A)
  where

  sim-prop-equivalence-relation-tuple : (n : ℕ) → Relation-Prop l2 (tuple A n)
  sim-prop-equivalence-relation-tuple n =
    prop-tuple-Relation-Prop (prop-equivalence-relation R) n

  sim-equivalence-relation-tuple : (n : ℕ) → Relation l2 (tuple A n)
  sim-equivalence-relation-tuple n =
    type-Relation-Prop (sim-prop-equivalence-relation-tuple n)

  abstract
    refl-sim-equivalence-relation-tuple :
      (n : ℕ) → is-reflexive (sim-equivalence-relation-tuple n)
    refl-sim-equivalence-relation-tuple =
      refl-rel-tuple-Relation
        ( sim-equivalence-relation R)
        ( refl-equivalence-relation R)

    symmetric-sim-equivalence-relation-tuple :
      (n : ℕ) → is-symmetric (sim-equivalence-relation-tuple n)
    symmetric-sim-equivalence-relation-tuple =
      symmetric-rel-tuple-Relation
        ( sim-equivalence-relation R)
        ( symmetric-equivalence-relation R)

    transitive-sim-equivalence-relation-tuple :
      (n : ℕ) → is-transitive (sim-equivalence-relation-tuple n)
    transitive-sim-equivalence-relation-tuple =
      transitive-rel-tuple-Relation
        ( sim-equivalence-relation R)
        ( transitive-equivalence-relation R)

  equivalence-relation-tuple : (n : ℕ) → equivalence-relation l2 (tuple A n)
  equivalence-relation-tuple n =
    ( sim-prop-equivalence-relation-tuple n ,
      refl-sim-equivalence-relation-tuple n ,
      symmetric-sim-equivalence-relation-tuple n ,
      transitive-sim-equivalence-relation-tuple n)
```
