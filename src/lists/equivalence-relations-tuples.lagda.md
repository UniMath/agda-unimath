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
open import foundation.raising-universe-levels-unit-type
open import foundation.unit-type
open import foundation.universe-levels

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
  sim-prop-equivalence-relation-tuple 0 empty-tuple empty-tuple =
    raise-unit-Prop l2
  sim-prop-equivalence-relation-tuple (succ-ℕ n) (x ∷ xs) (y ∷ ys) =
    ( prop-equivalence-relation R x y) ∧
    ( sim-prop-equivalence-relation-tuple n xs ys)

  sim-equivalence-relation-tuple : (n : ℕ) → Relation l2 (tuple A n)
  sim-equivalence-relation-tuple n =
    type-Relation-Prop (sim-prop-equivalence-relation-tuple n)

  abstract
    refl-sim-equivalence-relation-tuple :
      (n : ℕ) → is-reflexive (sim-equivalence-relation-tuple n)
    refl-sim-equivalence-relation-tuple 0 empty-tuple = map-raise star
    refl-sim-equivalence-relation-tuple (succ-ℕ n) (x ∷ xs) =
      ( refl-equivalence-relation R x ,
        refl-sim-equivalence-relation-tuple n xs)

    symmetric-sim-equivalence-relation-tuple :
      (n : ℕ) → is-symmetric (sim-equivalence-relation-tuple n)
    symmetric-sim-equivalence-relation-tuple 0 empty-tuple empty-tuple 0~0 = 0~0
    symmetric-sim-equivalence-relation-tuple
      (succ-ℕ n) (x ∷ xs) (y ∷ ys) (x~y , xs~ys) =
      ( symmetric-equivalence-relation R x y x~y ,
        symmetric-sim-equivalence-relation-tuple n xs ys xs~ys)

    transitive-sim-equivalence-relation-tuple :
      (n : ℕ) → is-transitive (sim-equivalence-relation-tuple n)
    transitive-sim-equivalence-relation-tuple
      0 empty-tuple empty-tuple empty-tuple 0~0 _ = 0~0
    transitive-sim-equivalence-relation-tuple
      (succ-ℕ n) (x ∷ xs) (y ∷ ys) (z ∷ zs) (y~z , ys~zs) (x~y , xs~ys) =
      ( transitive-equivalence-relation R x y z y~z x~y ,
        transitive-sim-equivalence-relation-tuple n xs ys zs ys~zs xs~ys)

  equivalence-relation-tuple : (n : ℕ) → equivalence-relation l2 (tuple A n)
  equivalence-relation-tuple n =
    ( sim-prop-equivalence-relation-tuple n ,
      refl-sim-equivalence-relation-tuple n ,
      symmetric-sim-equivalence-relation-tuple n ,
      transitive-sim-equivalence-relation-tuple n)
```
