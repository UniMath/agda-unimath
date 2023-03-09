# Decidable equivalence relations on finite types

```agda
module univalent-combinatorics.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equivalence-relations
open import foundation.decidable-relations
open import foundation.decidable-types
open import foundation.equivalence-relations
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A decidable equivalence relation on a finite type is an equivalence relation `R` such that each `R x y` is a decidable proposition.

## Definition

```agda
Decidable-Equivalence-Relation-𝔽 :
  {l1 : Level} (l2 : Level) (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation-𝔽 l2 X =
  Decidable-Equivalence-Relation l2 (type-𝔽 X)

module _
  {l1 l2 : Level} (X : 𝔽 l1) (R : Decidable-Equivalence-Relation-𝔽 l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation-𝔽 :
    Decidable-Relation l2 (type-𝔽 X)
  decidable-relation-Decidable-Equivalence-Relation-𝔽 =
    decidable-relation-Decidable-Equivalence-Relation R

  relation-Decidable-Equivalence-Relation-𝔽 :
    type-𝔽 X → type-𝔽 X → Prop l2
  relation-Decidable-Equivalence-Relation-𝔽 =
    relation-Decidable-Equivalence-Relation R

  sim-Decidable-Equivalence-Relation-𝔽 : type-𝔽 X → type-𝔽 X → UU l2
  sim-Decidable-Equivalence-Relation-𝔽 =
    sim-Decidable-Equivalence-Relation R

  is-prop-sim-Decidable-Equivalence-Relation-𝔽 :
    (x y : type-𝔽 X) → is-prop (sim-Decidable-Equivalence-Relation-𝔽 x y)
  is-prop-sim-Decidable-Equivalence-Relation-𝔽 =
    is-prop-sim-Decidable-Equivalence-Relation R

  is-decidable-sim-Decidable-Equivalence-Relation-𝔽 :
    (x y : type-𝔽 X) → is-decidable (sim-Decidable-Equivalence-Relation-𝔽 x y)
  is-decidable-sim-Decidable-Equivalence-Relation-𝔽 =
    is-decidable-sim-Decidable-Equivalence-Relation R

  is-equivalence-relation-Decidable-Equivalence-Relation-𝔽 :
    is-equivalence-relation relation-Decidable-Equivalence-Relation-𝔽
  is-equivalence-relation-Decidable-Equivalence-Relation-𝔽 =
    is-equivalence-relation-Decidable-Equivalence-Relation R

  equivalence-relation-Decidable-Equivalence-Relation-𝔽 :
    Eq-Rel l2 (type-𝔽 X)
  equivalence-relation-Decidable-Equivalence-Relation-𝔽 =
    equivalence-relation-Decidable-Equivalence-Relation R

  refl-Decidable-Equivalence-Relation-𝔽 :
    {x : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x x
  refl-Decidable-Equivalence-Relation-𝔽 =
    refl-Decidable-Equivalence-Relation R

  symmetric-Decidable-Equivalence-Relation-𝔽 :
    {x y : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x y →
    sim-Decidable-Equivalence-Relation-𝔽 y x
  symmetric-Decidable-Equivalence-Relation-𝔽 =
    symmetric-Decidable-Equivalence-Relation R

  transitive-Decidable-Equivalence-Relation-𝔽 :
    {x y z : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x y →
    sim-Decidable-Equivalence-Relation-𝔽 y z →
    sim-Decidable-Equivalence-Relation-𝔽 x z
  transitive-Decidable-Equivalence-Relation-𝔽 =
    transitive-Decidable-Equivalence-Relation R
```

## Properties

### The type of decidable equivalence relations on a finite type is finite

### The number of decidable equivalence relations on a finite type is a Stirling number of the second kind
