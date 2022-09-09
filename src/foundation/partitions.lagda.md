---
title: Partitions
---

```agda
module foundation.partitions where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.locally-small-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.small-types
open import foundation.subtypes
open import foundation.surjective-maps
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

  large-block-partition : UU (l1 ⊔ lsuc l2 ⊔ l3)
  large-block-partition = type-subtype subtype-partition

  inhabited-subtype-large-block-partition :
    large-block-partition → inhabited-subtype l2 A
  inhabited-subtype-large-block-partition =
    inclusion-subtype subtype-partition

  subtype-large-block-partition :
    large-block-partition → subtype l2 A
  subtype-large-block-partition =
    subtype-inhabited-subtype ∘ inhabited-subtype-large-block-partition

  is-inhabited-subtype-large-block-partition :
    (B : large-block-partition) →
    is-inhabited-subtype (subtype-large-block-partition B)
  is-inhabited-subtype-large-block-partition B =
    is-inhabited-subtype-inhabited-subtype
      ( inhabited-subtype-large-block-partition B)

  type-large-block-partition : large-block-partition → UU (l1 ⊔ l2)
  type-large-block-partition Q =
    type-inhabited-subtype (inhabited-subtype-large-block-partition Q)

  is-in-large-block-partition : large-block-partition → A → UU l2
  is-in-large-block-partition Q =
    is-in-inhabited-subtype (inhabited-subtype-large-block-partition Q)

  large-block-element-partition : A → large-block-partition
  pr1 (large-block-element-partition a) =
    pr1 (center (is-partition-subtype-partition a))
  pr2 (large-block-element-partition a) =
    pr1 (pr2 (center (is-partition-subtype-partition a)))

  is-surjective-large-block-element-partition :
    is-surjective large-block-element-partition
  is-surjective-large-block-element-partition B =
    apply-universal-property-trunc-Prop
      ( is-inhabited-subtype-large-block-partition B)
      ( trunc-Prop (fib large-block-element-partition B))
      ( λ (a , u) →
        unit-trunc-Prop
          ( pair
            ( a)
            ( eq-type-subtype
              ( subtype-partition)
              ( ap
                ( pr1)
                ( contraction
                  ( is-partition-subtype-partition a)
                  ( pair
                    ( inhabited-subtype-large-block-partition B)
                    ( pair (pr2 B) u)))))))

  is-locally-small-large-block-partition :
    is-locally-small (l1 ⊔ l2) large-block-partition
  is-locally-small-large-block-partition =
    is-locally-small-type-subtype
      ( subtype-partition)
      ( is-locally-small-inhabited-subtype is-small')
  
  is-small-large-block-partition :
    is-small (l1 ⊔ l2) large-block-partition
  is-small-large-block-partition =
    is-small-is-surjective
      ( is-surjective-large-block-element-partition)
      ( is-small-lmax l2 A)
      ( is-locally-small-large-block-partition)

  block-partition : UU (l1 ⊔ l2)
  block-partition = type-is-small is-small-large-block-partition

  compute-block-partition : large-block-partition ≃ block-partition
  compute-block-partition = equiv-is-small is-small-large-block-partition

  map-compute-block-partition : large-block-partition → block-partition
  map-compute-block-partition = map-equiv compute-block-partition

  map-inv-compute-block-partition : block-partition → large-block-partition
  map-inv-compute-block-partition =
    map-inv-equiv compute-block-partition

  issec-map-inv-compute-block-partition :
    ( map-compute-block-partition ∘ map-inv-compute-block-partition) ~ id
  issec-map-inv-compute-block-partition =
    issec-map-inv-equiv compute-block-partition

  isretr-map-inv-compute-block-partition :
    ( map-inv-compute-block-partition ∘ map-compute-block-partition) ~ id
  isretr-map-inv-compute-block-partition =
    isretr-map-inv-equiv compute-block-partition

  inhabited-subtype-block-partition : block-partition → inhabited-subtype l2 A
  inhabited-subtype-block-partition =
    inhabited-subtype-large-block-partition ∘ map-inv-compute-block-partition

  subtype-block-partition : block-partition → subtype l2 A
  subtype-block-partition =
    subtype-large-block-partition ∘ map-inv-compute-block-partition

  is-inhabited-subtype-block-partition :
    (B : block-partition) → is-inhabited-subtype (subtype-block-partition B)
  is-inhabited-subtype-block-partition B =
    is-inhabited-subtype-large-block-partition
      ( map-inv-compute-block-partition B)

  type-block-partition : block-partition → UU (l1 ⊔ l2)
  type-block-partition B =
    type-large-block-partition (map-inv-compute-block-partition B)

  is-in-block-partition : (B : block-partition) → A → UU l2
  is-in-block-partition B =
    is-in-large-block-partition (map-inv-compute-block-partition B)

  compute-is-in-block-partition :
    (B : large-block-partition) (x : A) →
    is-in-large-block-partition B x ≃
    is-in-block-partition (map-compute-block-partition B) x
  compute-is-in-block-partition B x =
    equiv-tr
      ( λ C → is-in-large-block-partition C x)
      ( inv (isretr-map-inv-compute-block-partition B))
```

## Properties

### Characterizing equality of partitions

```agda

```
