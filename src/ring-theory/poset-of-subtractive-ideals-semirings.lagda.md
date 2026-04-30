# The poset of subtractive ideals of a semiring

```agda
module ring-theory.poset-of-subtractive-ideals-semirings where
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

open import ring-theory.subtractive-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

The [subtractive ideals](ring-theory.subtractive-ideals-semirings.md) of a
[semiring](ring-theory.semirings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on subtractive ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-subtractive-ideal-Semiring :
    {l2 l3 : Level} →
    subtractive-ideal-Semiring l2 R →
    subtractive-ideal-Semiring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-subtractive-ideal-Semiring I J =
    leq-prop-subtype
      ( subset-subtractive-ideal-Semiring R I)
      ( subset-subtractive-ideal-Semiring R J)

  leq-subtractive-ideal-Semiring :
    {l2 l3 : Level} →
    subtractive-ideal-Semiring l2 R →
    subtractive-ideal-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-subtractive-ideal-Semiring I J =
    subset-subtractive-ideal-Semiring R I ⊆
    subset-subtractive-ideal-Semiring R J

  is-prop-leq-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    is-prop (leq-subtractive-ideal-Semiring I J)
  is-prop-leq-subtractive-ideal-Semiring I J =
    is-prop-leq-subtype
      ( subset-subtractive-ideal-Semiring R I)
      ( subset-subtractive-ideal-Semiring R J)

  refl-leq-subtractive-ideal-Semiring :
    {l2 : Level} → is-reflexive (leq-subtractive-ideal-Semiring {l2})
  refl-leq-subtractive-ideal-Semiring I =
    refl-leq-subtype (subset-subtractive-ideal-Semiring R I)

  transitive-leq-subtractive-ideal-Semiring :
    {l2 l3 l4 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R)
    (K : subtractive-ideal-Semiring l4 R) →
    leq-subtractive-ideal-Semiring J K →
    leq-subtractive-ideal-Semiring I J →
    leq-subtractive-ideal-Semiring I K
  transitive-leq-subtractive-ideal-Semiring I J K =
    transitive-leq-subtype
      ( subset-subtractive-ideal-Semiring R I)
      ( subset-subtractive-ideal-Semiring R J)
      ( subset-subtractive-ideal-Semiring R K)

  antisymmetric-leq-subtractive-ideal-Semiring :
    {l2 : Level} → is-antisymmetric (leq-subtractive-ideal-Semiring {l2})
  antisymmetric-leq-subtractive-ideal-Semiring I J U V =
    eq-has-same-elements-subtractive-ideal-Semiring R I J (λ x → U x , V x)
```

### The large poset of subtractive ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  subtractive-ideal-Semiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder subtractive-ideal-Semiring-Large-Preorder l =
    subtractive-ideal-Semiring l R
  leq-prop-Large-Preorder subtractive-ideal-Semiring-Large-Preorder =
    leq-prop-subtractive-ideal-Semiring R
  refl-leq-Large-Preorder subtractive-ideal-Semiring-Large-Preorder =
    refl-leq-subtractive-ideal-Semiring R
  transitive-leq-Large-Preorder subtractive-ideal-Semiring-Large-Preorder =
    transitive-leq-subtractive-ideal-Semiring R

  subtractive-ideal-Semiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset subtractive-ideal-Semiring-Large-Poset =
    subtractive-ideal-Semiring-Large-Preorder
  antisymmetric-leq-Large-Poset subtractive-ideal-Semiring-Large-Poset =
    antisymmetric-leq-subtractive-ideal-Semiring R
```

### The similarity relation on subtractive ideals in a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-subtractive-ideal-Semiring =
    sim-prop-Large-Poset (subtractive-ideal-Semiring-Large-Poset R)

  sim-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-subtractive-ideal-Semiring =
    sim-Large-Poset (subtractive-ideal-Semiring-Large-Poset R)

  is-prop-sim-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    is-prop (sim-subtractive-ideal-Semiring I J)
  is-prop-sim-subtractive-ideal-Semiring =
    is-prop-sim-Large-Poset (subtractive-ideal-Semiring-Large-Poset R)

  eq-sim-subtractive-ideal-Semiring :
    {l2 : Level}
    (I J : subtractive-ideal-Semiring l2 R) →
    sim-subtractive-ideal-Semiring I J → I ＝ J
  eq-sim-subtractive-ideal-Semiring =
    eq-sim-Large-Poset (subtractive-ideal-Semiring-Large-Poset R)

  has-same-elements-sim-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    sim-subtractive-ideal-Semiring I J →
    has-same-elements-subtractive-ideal-Semiring R I J
  pr1 (has-same-elements-sim-subtractive-ideal-Semiring I J H x) =
    pr1 H x
  pr2 (has-same-elements-sim-subtractive-ideal-Semiring I J H x) =
    pr2 H x

  sim-has-same-elements-subtractive-ideal-Semiring :
    {l2 l3 : Level}
    (I : subtractive-ideal-Semiring l2 R)
    (J : subtractive-ideal-Semiring l3 R) →
    has-same-elements-subtractive-ideal-Semiring R I J →
    sim-subtractive-ideal-Semiring I J
  pr1 (sim-has-same-elements-subtractive-ideal-Semiring I J H) x = pr1 (H x)
  pr2 (sim-has-same-elements-subtractive-ideal-Semiring I J H) x = pr2 (H x)
```

## Properties

### The forgetful function from subtractive ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-subtractive-ideal-Semiring :
    {l1 l2 : Level}
    (I : subtractive-ideal-Semiring l1 R)
    (J : subtractive-ideal-Semiring l2 R) →
    leq-subtractive-ideal-Semiring R I J →
    subset-subtractive-ideal-Semiring R I ⊆
    subset-subtractive-ideal-Semiring R J
  preserves-order-subset-subtractive-ideal-Semiring I J H = H

  subset-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( subtractive-ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder subset-ideal-hom-large-poset-Semiring =
    subset-subtractive-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subset-ideal-hom-large-poset-Semiring =
    preserves-order-subset-subtractive-ideal-Semiring
```
