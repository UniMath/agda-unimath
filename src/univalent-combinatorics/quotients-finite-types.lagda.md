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

The quotient of a finite type by a decidable equivalence relation is again a
finite type. In this file we set up some infrastructure for such quotients.

## Definition

```agda
module _
  {l1 l2 : Level} (X : 𝔽 l1) (R : Decidable-Equivalence-Relation-𝔽 l2 X)
  where

  equivalence-class-Decidable-Equivalence-Relation-𝔽 : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-Equivalence-Relation-𝔽 =
    im (decidable-relation-Decidable-Equivalence-Relation-𝔽 X R)

  is-finite-equivalence-class-Decidable-Equivalence-Relation-𝔽' :
    is-finite equivalence-class-Decidable-Equivalence-Relation-𝔽
  is-finite-equivalence-class-Decidable-Equivalence-Relation-𝔽' =
    is-finite-im
      ( is-finite-type-𝔽 X)
      ( has-decidable-equality-Subset-𝔽 X)

  quotient-𝔽 : 𝔽 (l1 ⊔ lsuc l2)
  pr1 quotient-𝔽 = equivalence-class-Decidable-Equivalence-Relation-𝔽
  pr2 quotient-𝔽 = is-finite-equivalence-class-Decidable-Equivalence-Relation-𝔽'
```
