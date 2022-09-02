---
title: Partitions
---

```agda
module foundation.partitions where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

## Idea

A partition of a type `A` is a subset `P` of the type of inhabited subsets of `A` such that for each `a : A` the type

```md
  Σ (Q : inhabited-subtype (A)), P(Q) × Q(a)
```

is contractible. In other words, it is a collection `P` of inhabited subtypes of `A` such that each element of `A` is in a unique inhabited subtype in `P`.

## Definition

```agda
is-partition-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  UU-Prop (l1 ⊔ lsuc l2 ⊔ l3)
is-partition-Prop {l1} {l2} {l3} {A} P =
  Π-Prop A
    ( λ x →
      is-contr-Prop
        ( Σ ( inhabited-subtype l2 A)
            ( λ Q → is-in-subtype P Q × is-in-inhabited-subtype Q x)))

is-partition :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  UU (l1 ⊔ lsuc l2 ⊔ l3)
is-partition P = type-Prop (is-partition-Prop P)

partition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition {l1} l2 l3 A = type-subtype (is-partition-Prop {l1} {l2} {l3} {A})

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  subtype-partition : subtype l3 (inhabited-subtype l2 A)
  subtype-partition = pr1 P

  is-partition-subtype-partition : is-partition subtype-partition
  is-partition-subtype-partition = pr2 P

  is-in-subtype-partition : inhabited-subtype l2 A → UU l3
  is-in-subtype-partition = is-in-subtype subtype-partition

  block-partition : UU (l1 ⊔ lsuc l2 ⊔ l3)
  block-partition = type-subtype subtype-partition

  inhabited-subtype-block-partition : block-partition → inhabited-subtype l2 A
  inhabited-subtype-block-partition = inclusion-subtype subtype-partition

  type-block-partition : block-partition → UU (l1 ⊔ l2)
  type-block-partition Q =
    type-inhabited-subtype (inhabited-subtype-block-partition Q)

  is-in-block-partition : block-partition → A → UU l2
  is-in-block-partition Q =
    is-in-inhabited-subtype (inhabited-subtype-block-partition Q)
```
