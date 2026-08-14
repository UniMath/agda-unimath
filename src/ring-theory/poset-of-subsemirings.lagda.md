# The poset of subsemirings

```agda
module ring-theory.poset-of-subsemirings where
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

open import ring-theory.subsemirings
open import ring-theory.semirings
```

</details>

## Idea

The [subsemirings](ring-theory.nonunital-subsemirings.md) of a
[semiring](ring-theory.semirings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on subsemirings

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-Subsemiring :
    {l2 l3 : Level} →
    Subsemiring l2 R → Subsemiring l3 R →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-Subsemiring I J =
    leq-prop-subtype
      ( subset-Subsemiring R I)
      ( subset-Subsemiring R J)

  leq-Subsemiring :
    {l2 l3 : Level} →
    Subsemiring l2 R → Subsemiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-Subsemiring I J =
    subset-Subsemiring R I ⊆ subset-Subsemiring R J

  is-prop-leq-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    is-prop (leq-Subsemiring I J)
  is-prop-leq-Subsemiring I J =
    is-prop-leq-subtype
      ( subset-Subsemiring R I)
      ( subset-Subsemiring R J)

  refl-leq-Subsemiring :
    {l2 : Level} → is-reflexive (leq-Subsemiring {l2})
  refl-leq-Subsemiring I =
    refl-leq-subtype (subset-Subsemiring R I)

  transitive-leq-Subsemiring :
    {l2 l3 l4 : Level}
    (I : Subsemiring l2 R)
    (J : Subsemiring l3 R)
    (K : Subsemiring l4 R) →
    leq-Subsemiring J K →
    leq-Subsemiring I J →
    leq-Subsemiring I K
  transitive-leq-Subsemiring I J K =
    transitive-leq-subtype
      ( subset-Subsemiring R I)
      ( subset-Subsemiring R J)
      ( subset-Subsemiring R K)

  antisymmetric-leq-Subsemiring :
    {l2 : Level} → is-antisymmetric (leq-Subsemiring {l2})
  antisymmetric-leq-Subsemiring I J U V =
    eq-has-same-elements-Subsemiring R I J (λ x → U x , V x)
```

### The large poset of subsemirings

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  Subsemiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder Subsemiring-Large-Preorder l =
    Subsemiring l R
  leq-prop-Large-Preorder Subsemiring-Large-Preorder =
    leq-prop-Subsemiring R
  refl-leq-Large-Preorder Subsemiring-Large-Preorder =
    refl-leq-Subsemiring R
  transitive-leq-Large-Preorder Subsemiring-Large-Preorder =
    transitive-leq-Subsemiring R

  Subsemiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset Subsemiring-Large-Poset =
    Subsemiring-Large-Preorder
  antisymmetric-leq-Large-Poset Subsemiring-Large-Poset =
    antisymmetric-leq-Subsemiring R
```

### The similarity relation on subsemirings in a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-Subsemiring =
    sim-prop-Large-Poset (Subsemiring-Large-Poset R)

  sim-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-Subsemiring = sim-Large-Poset (Subsemiring-Large-Poset R)

  is-prop-sim-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    is-prop (sim-Subsemiring I J)
  is-prop-sim-Subsemiring =
    is-prop-sim-Large-Poset (Subsemiring-Large-Poset R)

  eq-sim-Subsemiring :
    {l2 : Level}
    (I J : Subsemiring l2 R) → sim-Subsemiring I J → I ＝ J
  eq-sim-Subsemiring = eq-sim-Large-Poset (Subsemiring-Large-Poset R)

  has-same-elements-sim-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    sim-Subsemiring I J → has-same-elements-Subsemiring R I J
  pr1 (has-same-elements-sim-Subsemiring I J H x) =
    pr1 H x
  pr2 (has-same-elements-sim-Subsemiring I J H x) =
    pr2 H x

  sim-has-same-elements-Subsemiring :
    {l2 l3 : Level}
    (I : Subsemiring l2 R) (J : Subsemiring l3 R) →
    has-same-elements-Subsemiring R I J → sim-Subsemiring I J
  pr1 (sim-has-same-elements-Subsemiring I J H) x = pr1 (H x)
  pr2 (sim-has-same-elements-Subsemiring I J H) x = pr2 (H x)
```

## Properties

### The forgetful function from subsemirings to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-Subsemiring :
    {l1 l2 : Level}
    (I : Subsemiring l1 R) (J : Subsemiring l2 R) →
    leq-Subsemiring R I J →
    subset-Subsemiring R I ⊆ subset-Subsemiring R J
  preserves-order-subset-Subsemiring I J H = H

  subset-subsemiring-hom-large-poset-Subsemiring :
    hom-Large-Poset
      ( λ l → l)
      ( Subsemiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder subset-subsemiring-hom-large-poset-Subsemiring =
    subset-Subsemiring R
  preserves-order-hom-Large-Preorder
    subset-subsemiring-hom-large-poset-Subsemiring =
    preserves-order-subset-Subsemiring
```
