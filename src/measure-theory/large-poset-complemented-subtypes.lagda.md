# The large poset of complemented subtypes

```agda
module measure-theory.large-poset-complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import measure-theory.apart-subtypes
open import measure-theory.complemented-subtypes

open import order-theory.large-posets
open import order-theory.large-preorders
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  leq-prop-complemented-subtype-Type-With-Apartness :
    Large-Relation-Prop
      ( λ l l' → l1 ⊔ l ⊔ l')
      ( complemented-subtype-Type-With-Apartness X)
  leq-prop-complemented-subtype-Type-With-Apartness (A , A' , _) (B , B' , _) =
    leq-prop-subtype A B ∧ leq-prop-subtype B' A'

  leq-complemented-subtype-Type-With-Apartness :
    Large-Relation
      ( λ l l' → l1 ⊔ l ⊔ l')
      ( complemented-subtype-Type-With-Apartness X)
  leq-complemented-subtype-Type-With-Apartness A B =
    type-Prop (leq-prop-complemented-subtype-Type-With-Apartness A B)
```

## Properties

### The inequality relation on complemented subtypes is reflexive

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  refl-leq-complemented-subtype-Type-With-Apartness :
    is-reflexive-Large-Relation-Prop
      ( complemented-subtype-Type-With-Apartness X)
      ( leq-prop-complemented-subtype-Type-With-Apartness X)
  refl-leq-complemented-subtype-Type-With-Apartness (A , A' , _) =
    ( refl-leq-subtype A , refl-leq-subtype A')
```

### The inequality relation on complemented subtypes is transitive

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  transitive-leq-complemented-subtype-Type-With-Apartness :
    is-transitive-Large-Relation-Prop
      ( complemented-subtype-Type-With-Apartness X)
      ( leq-prop-complemented-subtype-Type-With-Apartness X)
  transitive-leq-complemented-subtype-Type-With-Apartness
    (A , A' , _) (B , B' , _) (C , C' , _) (B⊆C , C'⊆B') (A⊆B , B'⊆A') =
    ( transitive-leq-subtype A B C B⊆C A⊆B ,
      transitive-leq-subtype C' B' A' B'⊆A' C'⊆B')
```

### The inequality relation on complemented subtypes is antisymmetric

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  antisymmetric-leq-complemented-subtype-Type-With-Apartness :
    is-antisymmetric-Large-Relation-Prop
      ( complemented-subtype-Type-With-Apartness X)
      ( leq-prop-complemented-subtype-Type-With-Apartness X)
  antisymmetric-leq-complemented-subtype-Type-With-Apartness
    (A , A' , _) (B , B' , _) (A⊆B , B'⊆A') (B⊆A , A'⊆B')
    with eq-sim-subtype A B (A⊆B , B⊆A)
  ... | refl =
    eq-pair-eq-fiber
      ( eq-type-subtype
        ( apart-prop-subtype-Type-With-Apartness X A)
        ( eq-sim-subtype A' B' (A'⊆B' , B'⊆A')))
```

### The inequality relation on complemented subtypes forms a large poset

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  large-preorder-complemented-subtype-Type-With-Apartness :
    Large-Preorder (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l ⊔ l')
  large-preorder-complemented-subtype-Type-With-Apartness =
    λ where
      .type-Large-Preorder → complemented-subtype-Type-With-Apartness X
      .leq-prop-Large-Preorder →
        leq-prop-complemented-subtype-Type-With-Apartness X
      .refl-leq-Large-Preorder →
        refl-leq-complemented-subtype-Type-With-Apartness X
      .transitive-leq-Large-Preorder →
        transitive-leq-complemented-subtype-Type-With-Apartness X

  large-poset-complemented-subtype-Type-With-Apartness :
    Large-Poset (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l ⊔ l')
  large-poset-complemented-subtype-Type-With-Apartness =
    λ where
      .large-preorder-Large-Poset →
        large-preorder-complemented-subtype-Type-With-Apartness
      .antisymmetric-leq-Large-Poset →
        antisymmetric-leq-complemented-subtype-Type-With-Apartness X
```
