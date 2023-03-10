# Subgroups of finite groups

```agda
module finite-group-theory.subgroups-finite-groups where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-groups
open import finite-group-theory.finite-semigroups

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.decidable-subgroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.semigroups
open import group-theory.subgroups

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A finite subgroup of a finite group `G` is a decidable subgroup of `G`.

## Definitions

### Decidable subsets of groups

```agda
decidable-subset-Group-𝔽 :
  (l : Level) {l1 : Level} (G : Group-𝔽 l1) → UU (lsuc l ⊔ l1)
decidable-subset-Group-𝔽 l G =
  decidable-subset-Group l (group-Group-𝔽 G)

is-set-decidable-subset-Group-𝔽 :
  (l : Level) {l1 : Level} (G : Group-𝔽 l1) →
  is-set (decidable-subset-Group-𝔽 l G)
is-set-decidable-subset-Group-𝔽 l G =
  is-set-decidable-subset-Group l (group-Group-𝔽 G)

module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (P : decidable-subset-Group-𝔽 l2 G)
  where

  subset-decidable-subset-Group-𝔽 : subset-Group l2 (group-Group-𝔽 G)
  subset-decidable-subset-Group-𝔽 =
    subset-decidable-subset-Group (group-Group-𝔽 G) P
```

### Finite subgroups of finite groups

By default, finite subgroups of finite groups are considered to be decidable. Indeed, one can prove that if a subgroup of a finite group has a finite underlying type, then it must be a decidable subgroup.

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (P : decidable-subset-Group-𝔽 l2 G)
  where

  contains-unit-decidable-subset-finite-group-Prop : Prop l2
  contains-unit-decidable-subset-finite-group-Prop =
    contains-unit-decidable-subset-group-Prop
      ( group-Group-𝔽 G)
      ( P)

  contains-unit-decidable-subset-Group-𝔽 : UU l2
  contains-unit-decidable-subset-Group-𝔽 =
    contains-unit-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-prop-contains-unit-decidable-subset-Group-𝔽 :
    is-prop contains-unit-decidable-subset-Group-𝔽
  is-prop-contains-unit-decidable-subset-Group-𝔽 =
    is-prop-contains-unit-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-closed-under-mul-decidable-subset-finite-group-Prop : Prop (l1 ⊔ l2)
  is-closed-under-mul-decidable-subset-finite-group-Prop =
    is-closed-under-mul-decidable-subset-group-Prop
      ( group-Group-𝔽 G)
      ( P)

  is-closed-under-mul-decidable-subset-Group-𝔽 : UU (l1 ⊔ l2)
  is-closed-under-mul-decidable-subset-Group-𝔽 =
    is-closed-under-mul-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-prop-is-closed-under-mul-decidable-subset-Group-𝔽 :
    is-prop is-closed-under-mul-decidable-subset-Group-𝔽
  is-prop-is-closed-under-mul-decidable-subset-Group-𝔽 =
    is-prop-is-closed-under-mul-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-closed-under-inv-decidable-subset-finite-group-Prop : Prop (l1 ⊔ l2)
  is-closed-under-inv-decidable-subset-finite-group-Prop =
    is-closed-under-inv-decidable-subset-group-Prop
      ( group-Group-𝔽 G)
      ( P)

  is-closed-under-inv-decidable-subset-Group-𝔽 : UU (l1 ⊔ l2)
  is-closed-under-inv-decidable-subset-Group-𝔽 =
    is-closed-under-inv-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-prop-is-closed-under-inv-decidable-subset-Group-𝔽 :
    is-prop is-closed-under-inv-decidable-subset-Group-𝔽
  is-prop-is-closed-under-inv-decidable-subset-Group-𝔽 =
    is-prop-is-closed-under-inv-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-subgroup-decidable-subset-finite-group-Prop : Prop (l1 ⊔ l2)
  is-subgroup-decidable-subset-finite-group-Prop =
    is-subgroup-decidable-subset-group-Prop
      ( group-Group-𝔽 G)
      ( P)

  is-subgroup-decidable-subset-Group-𝔽 : UU (l1 ⊔ l2)
  is-subgroup-decidable-subset-Group-𝔽 =
    is-subgroup-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

  is-prop-is-subgroup-decidable-subset-Group-𝔽 :
    is-prop is-subgroup-decidable-subset-Group-𝔽
  is-prop-is-subgroup-decidable-subset-Group-𝔽 =
    is-prop-is-subgroup-decidable-subset-Group
      ( group-Group-𝔽 G)
      ( P)

Subgroup-𝔽 :
  (l : Level) {l1 : Level} (G : Group-𝔽 l1) → UU (lsuc l ⊔ l1)
Subgroup-𝔽 l G = Decidable-Subgroup l (group-Group-𝔽 G)

module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  decidable-subset-Subgroup-𝔽 : decidable-subset-Group l2 (group-Group-𝔽 G)
  decidable-subset-Subgroup-𝔽 =
    decidable-subset-Decidable-Subgroup (group-Group-𝔽 G) H

  subset-Subgroup-𝔽 : subset-Group l2 (group-Group-𝔽 G)
  subset-Subgroup-𝔽 = subset-Decidable-Subgroup (group-Group-𝔽 G) H

  is-subgroup-subset-Subgroup-𝔽 :
    is-subgroup-subset-Group (group-Group-𝔽 G) subset-Subgroup-𝔽
  is-subgroup-subset-Subgroup-𝔽 =
    is-subgroup-subset-Decidable-Subgroup (group-Group-𝔽 G) H

  subgroup-Subgroup-𝔽 : Subgroup l2 (group-Group-𝔽 G)
  subgroup-Subgroup-𝔽 = subgroup-Decidable-Subgroup (group-Group-𝔽 G) H

  type-Subgroup-𝔽 : UU (l1 ⊔ l2)
  type-Subgroup-𝔽 = type-Decidable-Subgroup (group-Group-𝔽 G) H

  is-finite-type-Subgroup-𝔽 : is-finite type-Subgroup-𝔽
  is-finite-type-Subgroup-𝔽 =
    is-finite-type-subset-𝔽 (finite-type-Group-𝔽 G) decidable-subset-Subgroup-𝔽

  finite-type-Subgroup-𝔽 : 𝔽 (l1 ⊔ l2)
  finite-type-Subgroup-𝔽 =
    finite-type-subset-𝔽 (finite-type-Group-𝔽 G) decidable-subset-Subgroup-𝔽

  inclusion-Subgroup-𝔽 : type-Subgroup-𝔽 → type-Group-𝔽 G
  inclusion-Subgroup-𝔽 = inclusion-Decidable-Subgroup (group-Group-𝔽 G) H

  is-emb-inclusion-Subgroup-𝔽 : is-emb inclusion-Subgroup-𝔽
  is-emb-inclusion-Subgroup-𝔽 =
    is-emb-inclusion-Decidable-Subgroup (group-Group-𝔽 G) H

  emb-inclusion-Subgroup-𝔽 : type-Subgroup-𝔽 ↪ type-Group-𝔽 G
  emb-inclusion-Subgroup-𝔽 =
    emb-inclusion-Decidable-Subgroup (group-Group-𝔽 G) H

  is-in-Subgroup-𝔽 : type-Group-𝔽 G → UU l2
  is-in-Subgroup-𝔽 = is-in-Decidable-Subgroup (group-Group-𝔽 G) H

  is-in-subgroup-inclusion-Subgroup-𝔽 :
    (x : type-Subgroup-𝔽) → is-in-Subgroup-𝔽 (inclusion-Subgroup-𝔽 x)
  is-in-subgroup-inclusion-Subgroup-𝔽 =
    is-in-subgroup-inclusion-Decidable-Subgroup (group-Group-𝔽 G) H

  is-prop-is-in-Subgroup-𝔽 :
    (x : type-Group-𝔽 G) → is-prop (is-in-Subgroup-𝔽 x)
  is-prop-is-in-Subgroup-𝔽 =
    is-prop-is-in-Decidable-Subgroup (group-Group-𝔽 G) H

  contains-unit-Subgroup-𝔽 :
    contains-unit-subset-Group (group-Group-𝔽 G) subset-Subgroup-𝔽
  contains-unit-Subgroup-𝔽 =
    contains-unit-Decidable-Subgroup (group-Group-𝔽 G) H

  is-closed-under-mul-Subgroup-𝔽 :
    is-closed-under-mul-subset-Group (group-Group-𝔽 G) subset-Subgroup-𝔽
  is-closed-under-mul-Subgroup-𝔽 =
    is-closed-under-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  is-closed-under-inv-Subgroup-𝔽 :
    is-closed-under-inv-subset-Group (group-Group-𝔽 G) subset-Subgroup-𝔽
  is-closed-under-inv-Subgroup-𝔽 =
    is-closed-under-inv-Decidable-Subgroup (group-Group-𝔽 G) H

is-emb-decidable-subset-Subgroup-𝔽 :
  {l1 l2 : Level} (G : Group-𝔽 l1) →
  is-emb (decidable-subset-Subgroup-𝔽 {l2 = l2} G)
is-emb-decidable-subset-Subgroup-𝔽 G =
  is-emb-decidable-subset-Decidable-Subgroup (group-Group-𝔽 G)
```

### The underlying group of a decidable subgroup

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  type-group-Subgroup-𝔽 : UU (l1 ⊔ l2)
  type-group-Subgroup-𝔽 = type-Subgroup-𝔽 G H

  map-inclusion-group-Subgroup-𝔽 :
    type-group-Subgroup-𝔽 → type-Group-𝔽 G
  map-inclusion-group-Subgroup-𝔽 = inclusion-Subgroup-𝔽 G H

  is-emb-inclusion-group-Subgroup-𝔽 :
    is-emb map-inclusion-group-Subgroup-𝔽
  is-emb-inclusion-group-Subgroup-𝔽 = is-emb-inclusion-Subgroup-𝔽 G H

  eq-subgroup-eq-Group-𝔽 :
    {x y : type-Subgroup-𝔽 G H} →
    ( inclusion-Subgroup-𝔽 G H x ＝ inclusion-Subgroup-𝔽 G H y) → x ＝ y
  eq-subgroup-eq-Group-𝔽 =
    eq-decidable-subgroup-eq-group (group-Group-𝔽 G) H

  set-group-Subgroup-𝔽 : Set (l1 ⊔ l2)
  set-group-Subgroup-𝔽 = set-group-Decidable-Subgroup (group-Group-𝔽 G) H

  mul-Subgroup-𝔽 : (x y : type-Subgroup-𝔽 G H) → type-Subgroup-𝔽 G H
  mul-Subgroup-𝔽 = mul-Decidable-Subgroup (group-Group-𝔽 G) H

  associative-mul-Subgroup-𝔽 :
    (x y z : type-Subgroup-𝔽 G H) →
    mul-Subgroup-𝔽 (mul-Subgroup-𝔽 x y) z ＝
    mul-Subgroup-𝔽 x (mul-Subgroup-𝔽 y z)
  associative-mul-Subgroup-𝔽 =
    associative-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  unit-Subgroup-𝔽 : type-Subgroup-𝔽 G H
  unit-Subgroup-𝔽 = unit-Decidable-Subgroup (group-Group-𝔽 G) H

  left-unit-law-mul-Subgroup-𝔽 :
    (x : type-Subgroup-𝔽 G H) → mul-Subgroup-𝔽 unit-Subgroup-𝔽 x ＝ x
  left-unit-law-mul-Subgroup-𝔽 =
    left-unit-law-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  right-unit-law-mul-Subgroup-𝔽 :
    (x : type-Subgroup-𝔽 G H) → mul-Subgroup-𝔽 x unit-Subgroup-𝔽 ＝ x
  right-unit-law-mul-Subgroup-𝔽 =
    right-unit-law-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  inv-Subgroup-𝔽 : type-Subgroup-𝔽 G H → type-Subgroup-𝔽 G H
  inv-Subgroup-𝔽 = inv-Decidable-Subgroup (group-Group-𝔽 G) H

  left-inverse-law-mul-Subgroup-𝔽 :
    ( x : type-Subgroup-𝔽 G H) →
    mul-Subgroup-𝔽 (inv-Subgroup-𝔽 x) x ＝ unit-Subgroup-𝔽
  left-inverse-law-mul-Subgroup-𝔽 =
    left-inverse-law-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  right-inverse-law-mul-Subgroup-𝔽 :
    (x : type-Subgroup-𝔽 G H) →
    mul-Subgroup-𝔽 x (inv-Subgroup-𝔽 x) ＝ unit-Subgroup-𝔽
  right-inverse-law-mul-Subgroup-𝔽 =
    right-inverse-law-mul-Decidable-Subgroup (group-Group-𝔽 G) H

  finite-semigroup-Subgroup-𝔽 : Semigroup-𝔽 (l1 ⊔ l2)
  pr1 finite-semigroup-Subgroup-𝔽 = finite-type-Subgroup-𝔽 G H
  pr1 (pr2 finite-semigroup-Subgroup-𝔽) = mul-Subgroup-𝔽
  pr2 (pr2 finite-semigroup-Subgroup-𝔽) = associative-mul-Subgroup-𝔽

  finite-group-Subgroup-𝔽 : Group-𝔽 (l1 ⊔ l2)
  pr1 finite-group-Subgroup-𝔽 = finite-semigroup-Subgroup-𝔽
  pr1 (pr1 (pr2 finite-group-Subgroup-𝔽)) = unit-Subgroup-𝔽
  pr1 (pr2 (pr1 (pr2 finite-group-Subgroup-𝔽))) = left-unit-law-mul-Subgroup-𝔽
  pr2 (pr2 (pr1 (pr2 finite-group-Subgroup-𝔽))) = right-unit-law-mul-Subgroup-𝔽
  pr1 (pr2 (pr2 finite-group-Subgroup-𝔽)) = inv-Subgroup-𝔽
  pr1 (pr2 (pr2 (pr2 finite-group-Subgroup-𝔽))) =
    left-inverse-law-mul-Subgroup-𝔽
  pr2 (pr2 (pr2 (pr2 finite-group-Subgroup-𝔽))) =
    right-inverse-law-mul-Subgroup-𝔽

semigroup-Subgroup-𝔽 :
  {l1 l2 : Level} (G : Group-𝔽 l1) → Subgroup-𝔽 l2 G → Semigroup (l1 ⊔ l2)
semigroup-Subgroup-𝔽 G H =
  semigroup-Semigroup-𝔽 (finite-semigroup-Subgroup-𝔽 G H)

group-Subgroup-𝔽 :
  {l1 l2 : Level} (G : Group-𝔽 l1) → Subgroup-𝔽 l2 G → Group (l1 ⊔ l2)
group-Subgroup-𝔽 G H = group-Group-𝔽 (finite-group-Subgroup-𝔽 G H)
```

### The inclusion homomorphism of the underlying finite group of a finite subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  preserves-mul-inclusion-group-Subgroup-𝔽 :
    preserves-mul-Group
      ( group-Subgroup-𝔽 G H)
      ( group-Group-𝔽 G)
      ( inclusion-Subgroup-𝔽 G H)
  preserves-mul-inclusion-group-Subgroup-𝔽 =
    preserves-mul-inclusion-group-Decidable-Subgroup (group-Group-𝔽 G) H

  preserves-unit-inclusion-group-Subgroup-𝔽 :
    preserves-unit-Group
      ( group-Subgroup-𝔽 G H)
      ( group-Group-𝔽 G)
      ( inclusion-Subgroup-𝔽 G H)
  preserves-unit-inclusion-group-Subgroup-𝔽 =
    preserves-unit-inclusion-group-Decidable-Subgroup (group-Group-𝔽 G) H

  preserves-inverses-inclusion-group-Subgroup-𝔽 :
    preserves-inverses-Group
      ( group-Subgroup-𝔽 G H)
      ( group-Group-𝔽 G)
      ( inclusion-Subgroup-𝔽 G H)
  preserves-inverses-inclusion-group-Subgroup-𝔽 =
    preserves-inverses-inclusion-group-Decidable-Subgroup (group-Group-𝔽 G) H

  inclusion-group-Subgroup-𝔽 :
    type-hom-Group (group-Subgroup-𝔽 G H) (group-Group-𝔽 G)
  inclusion-group-Subgroup-𝔽 =
    inclusion-group-Decidable-Subgroup (group-Group-𝔽 G) H
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  has-same-elements-Subgroup-𝔽 :
    {l3 : Level} → Subgroup-𝔽 l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup-𝔽 =
    has-same-elements-Decidable-Subgroup (group-Group-𝔽 G) H

  extensionality-Subgroup-𝔽 :
    (K : Subgroup-𝔽 l2 G) → (H ＝ K) ≃ has-same-elements-Subgroup-𝔽 K
  extensionality-Subgroup-𝔽 =
    extensionality-Decidable-Subgroup (group-Group-𝔽 G) H
```

### Every finite subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`.

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  right-sim-Subgroup-𝔽 : (x y : type-Group-𝔽 G) → UU l2
  right-sim-Subgroup-𝔽 = right-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  is-prop-right-sim-Subgroup-𝔽 :
    (x y : type-Group-𝔽 G) → is-prop (right-sim-Subgroup-𝔽 x y)
  is-prop-right-sim-Subgroup-𝔽 =
    is-prop-right-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  prop-right-eq-rel-Subgroup-𝔽 :
    (x y : type-Group-𝔽 G) → Prop l2
  prop-right-eq-rel-Subgroup-𝔽 =
    prop-right-eq-rel-Decidable-Subgroup (group-Group-𝔽 G) H

  refl-right-sim-Subgroup-𝔽 :
    is-reflexive-Rel-Prop prop-right-eq-rel-Subgroup-𝔽
  refl-right-sim-Subgroup-𝔽 =
    refl-right-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  symm-right-sim-Subgroup-𝔽 :
    is-symmetric-Rel-Prop prop-right-eq-rel-Subgroup-𝔽
  symm-right-sim-Subgroup-𝔽 =
    symm-right-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  trans-right-sim-Subgroup-𝔽 :
    is-transitive-Rel-Prop prop-right-eq-rel-Subgroup-𝔽
  trans-right-sim-Subgroup-𝔽 =
    trans-right-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  right-eq-rel-Subgroup-𝔽 : Eq-Rel l2 (type-Group-𝔽 G)
  right-eq-rel-Subgroup-𝔽 =
    right-eq-rel-Decidable-Subgroup (group-Group-𝔽 G) H
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`.

```agda
module _
  {l1 l2 : Level} (G : Group-𝔽 l1) (H : Subgroup-𝔽 l2 G)
  where

  left-sim-Subgroup-𝔽 : (x y : type-Group-𝔽 G) → UU l2
  left-sim-Subgroup-𝔽 = left-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  is-prop-left-sim-Subgroup-𝔽 :
    (x y : type-Group-𝔽 G) → is-prop (left-sim-Subgroup-𝔽 x y)
  is-prop-left-sim-Subgroup-𝔽 =
    is-prop-left-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  prop-left-eq-rel-Subgroup-𝔽 : (x y : type-Group-𝔽 G) → Prop l2
  prop-left-eq-rel-Subgroup-𝔽 =
    prop-left-eq-rel-Decidable-Subgroup (group-Group-𝔽 G) H

  refl-left-sim-Subgroup-𝔽 :
    is-reflexive-Rel-Prop prop-left-eq-rel-Subgroup-𝔽
  refl-left-sim-Subgroup-𝔽 =
    refl-left-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  symmetric-left-sim-Subgroup-𝔽 :
    is-symmetric-Rel-Prop prop-left-eq-rel-Subgroup-𝔽
  symmetric-left-sim-Subgroup-𝔽 =
    symmetric-left-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  transitive-left-sim-Subgroup-𝔽 :
    is-transitive-Rel-Prop prop-left-eq-rel-Subgroup-𝔽
  transitive-left-sim-Subgroup-𝔽 =
    transitive-left-sim-Decidable-Subgroup (group-Group-𝔽 G) H

  left-eq-rel-Subgroup-𝔽 : Eq-Rel l2 (type-Group-𝔽 G)
  left-eq-rel-Subgroup-𝔽 =
    left-eq-rel-Decidable-Subgroup (group-Group-𝔽 G) H
```
