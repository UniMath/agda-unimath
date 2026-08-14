# The poset of ideals of a commutative semiring

```agda
module commutative-algebra.poset-of-ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.ideals-commutative-semirings
open import commutative-algebra.commutative-semirings

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

open import ring-theory.poset-of-ideals-semirings
```

</details>

## Idea

The [ideals](commutative-algebra.ideals-semirings.md) of a
[commutative semiring](commutative-algebra.commutative-semirings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on ideals

```agda
module _
  {l1 : Level} (A : Commutative-Semiring l1)
  where

  leq-prop-ideal-Commutative-Semiring :
    {l2 l3 : Level} →
    ideal-Commutative-Semiring l2 A →
    ideal-Commutative-Semiring l3 A →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-ideal-Commutative-Semiring =
    leq-prop-ideal-Semiring (semiring-Commutative-Semiring A)

  leq-ideal-Commutative-Semiring :
    {l2 l3 : Level} →
    ideal-Commutative-Semiring l2 A →
    ideal-Commutative-Semiring l3 A →
    UU (l1 ⊔ l2 ⊔ l3)
  leq-ideal-Commutative-Semiring =
    leq-ideal-Semiring (semiring-Commutative-Semiring A)

  is-prop-leq-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A)
    (J : ideal-Commutative-Semiring l3 A) →
    is-prop (leq-ideal-Commutative-Semiring I J)
  is-prop-leq-ideal-Commutative-Semiring =
    is-prop-leq-ideal-Semiring (semiring-Commutative-Semiring A)

  refl-leq-ideal-Commutative-Semiring :
    {l2 : Level} → is-reflexive (leq-ideal-Commutative-Semiring {l2})
  refl-leq-ideal-Commutative-Semiring =
    refl-leq-ideal-Semiring (semiring-Commutative-Semiring A)

  transitive-leq-ideal-Commutative-Semiring :
    {l2 l3 l4 : Level}
    (I : ideal-Commutative-Semiring l2 A)
    (J : ideal-Commutative-Semiring l3 A)
    (K : ideal-Commutative-Semiring l4 A) →
    leq-ideal-Commutative-Semiring J K →
    leq-ideal-Commutative-Semiring I J →
    leq-ideal-Commutative-Semiring I K
  transitive-leq-ideal-Commutative-Semiring =
    transitive-leq-ideal-Semiring (semiring-Commutative-Semiring A)

  antisymmetric-leq-ideal-Commutative-Semiring :
    {l2 : Level} → is-antisymmetric (leq-ideal-Commutative-Semiring {l2})
  antisymmetric-leq-ideal-Commutative-Semiring =
    antisymmetric-leq-ideal-Semiring (semiring-Commutative-Semiring A)
```

### The large poset of ideals

```agda
module _
  {l1 : Level} (A : Commutative-Semiring l1)
  where

  ideal-Commutative-Semiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  ideal-Commutative-Semiring-Large-Preorder =
    ideal-Semiring-Large-Preorder (semiring-Commutative-Semiring A)

  ideal-Commutative-Semiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  ideal-Commutative-Semiring-Large-Poset =
    ideal-Semiring-Large-Poset (semiring-Commutative-Semiring A)
```

### The similarity relation on ideals in a commutative semiring

```agda
module _
  {l1 : Level} (A : Commutative-Semiring l1)
  where

  sim-prop-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A) →
    (J : ideal-Commutative-Semiring l3 A) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-ideal-Commutative-Semiring =
    sim-prop-ideal-Semiring (semiring-Commutative-Semiring A)

  sim-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A) →
    (J : ideal-Commutative-Semiring l3 A) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-ideal-Commutative-Semiring =
    sim-ideal-Semiring (semiring-Commutative-Semiring A)

  is-prop-sim-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A) →
    (J : ideal-Commutative-Semiring l3 A) →
    is-prop (sim-ideal-Commutative-Semiring I J)
  is-prop-sim-ideal-Commutative-Semiring =
    is-prop-sim-ideal-Semiring (semiring-Commutative-Semiring A)

  eq-sim-ideal-Commutative-Semiring :
    {l2 : Level}
    (I J : ideal-Commutative-Semiring l2 A) →
    sim-ideal-Commutative-Semiring I J → I ＝ J
  eq-sim-ideal-Commutative-Semiring =
    eq-sim-ideal-Semiring (semiring-Commutative-Semiring A)
    
  has-same-elements-sim-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A) →
    (J : ideal-Commutative-Semiring l3 A) →
    sim-ideal-Commutative-Semiring I J →
    has-same-elements-ideal-Commutative-Semiring A I J
  has-same-elements-sim-ideal-Commutative-Semiring =
    has-same-elements-sim-ideal-Semiring (semiring-Commutative-Semiring A)

  sim-has-same-elements-ideal-Commutative-Semiring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Semiring l2 A) →
    (J : ideal-Commutative-Semiring l3 A) →
    has-same-elements-ideal-Commutative-Semiring A I J →
    sim-ideal-Commutative-Semiring I J
  sim-has-same-elements-ideal-Commutative-Semiring =
    sim-has-same-elements-ideal-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### The forgetful function from ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  preserves-order-subset-ideal-Commutative-Semiring :
    {l1 l2 : Level}
    (I : ideal-Commutative-Semiring l1 A)
    (J : ideal-Commutative-Semiring l2 A) →
    leq-ideal-Commutative-Semiring A I J →
    subset-ideal-Commutative-Semiring A I ⊆
    subset-ideal-Commutative-Semiring A J
  preserves-order-subset-ideal-Commutative-Semiring =
    preserves-order-subset-ideal-Semiring (semiring-Commutative-Semiring A)

  subset-ideal-hom-large-poset-Commutative-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Commutative-Semiring-Large-Poset A)
      ( powerset-Large-Poset (type-Commutative-Semiring A))
  subset-ideal-hom-large-poset-Commutative-Semiring =
    subset-ideal-hom-large-poset-Semiring (semiring-Commutative-Semiring A)
```
