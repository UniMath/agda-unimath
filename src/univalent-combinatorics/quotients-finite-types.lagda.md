# Quotients of finite types

```agda
module univalent-combinatorics.quotients-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-equivalence-relations
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
```

</details>

## Idea

The quotient of a [finite type](univalent-combinatorics.finite-types.md) by a
[decidable equivalence relation](foundation.decidable-equivalence-relations.md)
is again a finite type. In this file we set up some infrastructure for such
quotients.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1)
  (R : type-Decidable-Equivalence-Relation-Finite-Type l2 X)
  where

  equivalence-class-Decidable-Equivalence-Relation-Finite-Type :
    UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-Equivalence-Relation-Finite-Type =
    im (decidable-relation-Decidable-Equivalence-Relation-Finite-Type X R)

  is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type' :
    is-finite equivalence-class-Decidable-Equivalence-Relation-Finite-Type
  is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type' =
    is-finite-im
      ( is-finite-type-Finite-Type X)
      ( has-decidable-equality-Subset-Finite-Type X)

  quotient-Finite-Type : Finite-Type (l1 ⊔ lsuc l2)
  pr1 quotient-Finite-Type =
    equivalence-class-Decidable-Equivalence-Relation-Finite-Type
  pr2 quotient-Finite-Type =
    is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type'
```
