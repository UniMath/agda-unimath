# The poset of nonunital subsemirings

```agda
module ring-theory.poset-of-nonunital-subsemirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets

open import ring-theory.nonunital-subsemirings
open import ring-theory.semirings
```

</details>

## Idea

The [nonunital subsemirings](ring-theory.nonunital-subsemirings.md) of a
[semiring](ring-theory.semirings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on nonunital subsemirings

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-Nonunital-Subsemiring :
    {l2 l3 : Level} →
    Nonunital-Subsemiring l2 R → Nonunital-Subsemiring l3 R →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-Nonunital-Subsemiring I J =
    leq-prop-subtype
      ( subset-Nonunital-Subsemiring R I)
      ( subset-Nonunital-Subsemiring R J)

  leq-Nonunital-Subsemiring :
    {l2 l3 : Level} →
    Nonunital-Subsemiring l2 R → Nonunital-Subsemiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-Nonunital-Subsemiring I J =
    subset-Nonunital-Subsemiring R I ⊆ subset-Nonunital-Subsemiring R J

  is-prop-leq-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    is-prop (leq-Nonunital-Subsemiring I J)
  is-prop-leq-Nonunital-Subsemiring I J =
    is-prop-leq-subtype
      ( subset-Nonunital-Subsemiring R I)
      ( subset-Nonunital-Subsemiring R J)

  refl-leq-Nonunital-Subsemiring :
    {l2 : Level} → is-reflexive (leq-Nonunital-Subsemiring {l2})
  refl-leq-Nonunital-Subsemiring I =
    refl-leq-subtype (subset-Nonunital-Subsemiring R I)

  transitive-leq-Nonunital-Subsemiring :
    {l2 l3 l4 : Level}
    (I : Nonunital-Subsemiring l2 R)
    (J : Nonunital-Subsemiring l3 R)
    (K : Nonunital-Subsemiring l4 R) →
    leq-Nonunital-Subsemiring J K →
    leq-Nonunital-Subsemiring I J →
    leq-Nonunital-Subsemiring I K
  transitive-leq-Nonunital-Subsemiring I J K =
    transitive-leq-subtype
      ( subset-Nonunital-Subsemiring R I)
      ( subset-Nonunital-Subsemiring R J)
      ( subset-Nonunital-Subsemiring R K)

  antisymmetric-leq-Nonunital-Subsemiring :
    {l2 : Level} → is-antisymmetric (leq-Nonunital-Subsemiring {l2})
  antisymmetric-leq-Nonunital-Subsemiring I J U V =
    eq-has-same-elements-Nonunital-Subsemiring R I J (λ x → U x , V x)
```

### The large poset of nonunital subsemirings

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  Nonunital-Subsemiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder Nonunital-Subsemiring-Large-Preorder l =
    Nonunital-Subsemiring l R
  leq-prop-Large-Preorder Nonunital-Subsemiring-Large-Preorder =
    leq-prop-Nonunital-Subsemiring R
  refl-leq-Large-Preorder Nonunital-Subsemiring-Large-Preorder =
    refl-leq-Nonunital-Subsemiring R
  transitive-leq-Large-Preorder Nonunital-Subsemiring-Large-Preorder =
    transitive-leq-Nonunital-Subsemiring R

  Nonunital-Subsemiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset Nonunital-Subsemiring-Large-Poset =
    Nonunital-Subsemiring-Large-Preorder
  antisymmetric-leq-Large-Poset Nonunital-Subsemiring-Large-Poset =
    antisymmetric-leq-Nonunital-Subsemiring R
```

### The similarity relation on nonunital subsemirings

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-Nonunital-Subsemiring =
    sim-prop-Large-Poset (Nonunital-Subsemiring-Large-Poset R)

  sim-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-Nonunital-Subsemiring =
    sim-Large-Poset (Nonunital-Subsemiring-Large-Poset R)

  is-prop-sim-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    is-prop (sim-Nonunital-Subsemiring I J)
  is-prop-sim-Nonunital-Subsemiring =
    is-prop-sim-Large-Poset (Nonunital-Subsemiring-Large-Poset R)

  eq-sim-Nonunital-Subsemiring :
    {l2 : Level}
    (I J : Nonunital-Subsemiring l2 R) → sim-Nonunital-Subsemiring I J → I ＝ J
  eq-sim-Nonunital-Subsemiring =
    eq-sim-Large-Poset (Nonunital-Subsemiring-Large-Poset R)

  has-same-elements-sim-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    sim-Nonunital-Subsemiring I J →
    has-same-elements-Nonunital-Subsemiring R I J
  pr1 (has-same-elements-sim-Nonunital-Subsemiring I J H x) =
    pr1 H x
  pr2 (has-same-elements-sim-Nonunital-Subsemiring I J H x) =
    pr2 H x

  sim-has-same-elements-Nonunital-Subsemiring :
    {l2 l3 : Level}
    (I : Nonunital-Subsemiring l2 R) (J : Nonunital-Subsemiring l3 R) →
    has-same-elements-Nonunital-Subsemiring R I J →
    sim-Nonunital-Subsemiring I J
  pr1 (sim-has-same-elements-Nonunital-Subsemiring I J H) x = pr1 (H x)
  pr2 (sim-has-same-elements-Nonunital-Subsemiring I J H) x = pr2 (H x)
```

## Properties

### The forgetful function from nonunital subsemirings to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-Nonunital-Subsemiring :
    {l1 l2 : Level}
    (I : Nonunital-Subsemiring l1 R) (J : Nonunital-Subsemiring l2 R) →
    leq-Nonunital-Subsemiring R I J →
    subset-Nonunital-Subsemiring R I ⊆ subset-Nonunital-Subsemiring R J
  preserves-order-subset-Nonunital-Subsemiring I J H = H

  subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring :
    hom-Large-Poset
      ( λ l → l)
      ( Nonunital-Subsemiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder
    subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring =
    subset-Nonunital-Subsemiring R
  preserves-order-hom-Large-Preorder
    subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring =
    preserves-order-subset-Nonunital-Subsemiring
```
