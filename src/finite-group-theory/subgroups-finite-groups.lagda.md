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
open import group-theory.subsets-groups

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "finite subgroup" Disambiguation="of a finite group" Agda=Subgroup-Finite-Group}}
of a [finite group](finite-group-theory.finite-groups.md) `G` is a
[decidable subgroup](group-theory.decidable-subgroups.md) of `G`.

## Definitions

### Decidable subsets of groups

```agda
decidable-subset-Finite-Group :
  (l : Level) {l1 : Level} (G : Finite-Group l1) → UU (lsuc l ⊔ l1)
decidable-subset-Finite-Group l G =
  decidable-subset-Group l (group-Finite-Group G)

is-set-decidable-subset-Finite-Group :
  (l : Level) {l1 : Level} (G : Finite-Group l1) →
  is-set (decidable-subset-Finite-Group l G)
is-set-decidable-subset-Finite-Group l G =
  is-set-decidable-subset-Group l (group-Finite-Group G)

module _
  {l1 l2 : Level} (G : Finite-Group l1) (P : decidable-subset-Finite-Group l2 G)
  where

  subset-decidable-subset-Finite-Group : subset-Group l2 (group-Finite-Group G)
  subset-decidable-subset-Finite-Group =
    subset-decidable-subset-Group (group-Finite-Group G) P
```

### Finite subgroups of finite groups

By default, finite subgroups of finite groups are considered to be decidable.
Indeed, one can prove that if a subgroup of a finite group has a finite
underlying type, then it must be a decidable subgroup.

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (P : decidable-subset-Finite-Group l2 G)
  where

  contains-unit-prop-decidable-subset-Finite-Group : Prop l2
  contains-unit-prop-decidable-subset-Finite-Group =
    contains-unit-prop-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  contains-unit-decidable-subset-Finite-Group : UU l2
  contains-unit-decidable-subset-Finite-Group =
    contains-unit-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-prop-contains-unit-decidable-subset-Finite-Group :
    is-prop contains-unit-decidable-subset-Finite-Group
  is-prop-contains-unit-decidable-subset-Finite-Group =
    is-prop-contains-unit-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-closed-under-multiplication-prop-decidable-subset-Finite-Group :
    Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-decidable-subset-Finite-Group =
    is-closed-under-multiplication-prop-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-closed-under-multiplication-decidable-subset-Finite-Group : UU (l1 ⊔ l2)
  is-closed-under-multiplication-decidable-subset-Finite-Group =
    is-closed-under-multiplication-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-prop-is-closed-under-multiplication-decidable-subset-Finite-Group :
    is-prop is-closed-under-multiplication-decidable-subset-Finite-Group
  is-prop-is-closed-under-multiplication-decidable-subset-Finite-Group =
    is-prop-is-closed-under-multiplication-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-closed-under-inverses-prop-decidable-subset-Finite-Group : Prop (l1 ⊔ l2)
  is-closed-under-inverses-prop-decidable-subset-Finite-Group =
    is-closed-under-inverses-prop-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-closed-under-inverses-decidable-subset-Finite-Group : UU (l1 ⊔ l2)
  is-closed-under-inverses-decidable-subset-Finite-Group =
    is-closed-under-inverses-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-prop-is-closed-under-inverses-decidable-subset-Finite-Group :
    is-prop is-closed-under-inverses-decidable-subset-Finite-Group
  is-prop-is-closed-under-inverses-decidable-subset-Finite-Group =
    is-prop-is-closed-under-inverses-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-subgroup-prop-decidable-subset-Finite-Group : Prop (l1 ⊔ l2)
  is-subgroup-prop-decidable-subset-Finite-Group =
    is-subgroup-prop-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-subgroup-decidable-subset-Finite-Group : UU (l1 ⊔ l2)
  is-subgroup-decidable-subset-Finite-Group =
    is-subgroup-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

  is-prop-is-subgroup-decidable-subset-Finite-Group :
    is-prop is-subgroup-decidable-subset-Finite-Group
  is-prop-is-subgroup-decidable-subset-Finite-Group =
    is-prop-is-subgroup-decidable-subset-Group
      ( group-Finite-Group G)
      ( P)

Subgroup-Finite-Group :
  (l : Level) {l1 : Level} (G : Finite-Group l1) → UU (lsuc l ⊔ l1)
Subgroup-Finite-Group l G = Decidable-Subgroup l (group-Finite-Group G)

module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  decidable-subset-Subgroup-Finite-Group :
    decidable-subset-Group l2 (group-Finite-Group G)
  decidable-subset-Subgroup-Finite-Group =
    decidable-subset-Decidable-Subgroup (group-Finite-Group G) H

  subset-Subgroup-Finite-Group : subset-Group l2 (group-Finite-Group G)
  subset-Subgroup-Finite-Group =
    subset-Decidable-Subgroup (group-Finite-Group G) H

  is-subgroup-subset-Subgroup-Finite-Group :
    is-subgroup-subset-Group (group-Finite-Group G) subset-Subgroup-Finite-Group
  is-subgroup-subset-Subgroup-Finite-Group =
    is-subgroup-subset-Decidable-Subgroup (group-Finite-Group G) H

  subgroup-Subgroup-Finite-Group : Subgroup l2 (group-Finite-Group G)
  subgroup-Subgroup-Finite-Group =
    subgroup-Decidable-Subgroup (group-Finite-Group G) H

  type-Subgroup-Finite-Group : UU (l1 ⊔ l2)
  type-Subgroup-Finite-Group = type-Decidable-Subgroup (group-Finite-Group G) H

  is-finite-type-Subgroup-Finite-Group : is-finite type-Subgroup-Finite-Group
  is-finite-type-Subgroup-Finite-Group =
    is-finite-type-subset-Finite-Type
      ( finite-type-Finite-Group G)
      decidable-subset-Subgroup-Finite-Group

  finite-type-Subgroup-Finite-Group : Finite-Type (l1 ⊔ l2)
  finite-type-Subgroup-Finite-Group =
    finite-type-subset-Finite-Type
      ( finite-type-Finite-Group G)
      decidable-subset-Subgroup-Finite-Group

  inclusion-Subgroup-Finite-Group :
    type-Subgroup-Finite-Group → type-Finite-Group G
  inclusion-Subgroup-Finite-Group =
    inclusion-Decidable-Subgroup (group-Finite-Group G) H

  is-emb-inclusion-Subgroup-Finite-Group :
    is-emb inclusion-Subgroup-Finite-Group
  is-emb-inclusion-Subgroup-Finite-Group =
    is-emb-inclusion-Decidable-Subgroup (group-Finite-Group G) H

  emb-inclusion-Subgroup-Finite-Group :
    type-Subgroup-Finite-Group ↪ type-Finite-Group G
  emb-inclusion-Subgroup-Finite-Group =
    emb-inclusion-Decidable-Subgroup (group-Finite-Group G) H

  is-in-Subgroup-Finite-Group : type-Finite-Group G → UU l2
  is-in-Subgroup-Finite-Group =
    is-in-Decidable-Subgroup (group-Finite-Group G) H

  is-in-subgroup-inclusion-Subgroup-Finite-Group :
    (x : type-Subgroup-Finite-Group) →
    is-in-Subgroup-Finite-Group (inclusion-Subgroup-Finite-Group x)
  is-in-subgroup-inclusion-Subgroup-Finite-Group =
    is-in-subgroup-inclusion-Decidable-Subgroup (group-Finite-Group G) H

  is-prop-is-in-Subgroup-Finite-Group :
    (x : type-Finite-Group G) → is-prop (is-in-Subgroup-Finite-Group x)
  is-prop-is-in-Subgroup-Finite-Group =
    is-prop-is-in-Decidable-Subgroup (group-Finite-Group G) H

  contains-unit-Subgroup-Finite-Group :
    contains-unit-subset-Group
      ( group-Finite-Group G)
      subset-Subgroup-Finite-Group
  contains-unit-Subgroup-Finite-Group =
    contains-unit-Decidable-Subgroup (group-Finite-Group G) H

  is-closed-under-multiplication-Subgroup-Finite-Group :
    is-closed-under-multiplication-subset-Group
      ( group-Finite-Group G)
      ( subset-Subgroup-Finite-Group)
  is-closed-under-multiplication-Subgroup-Finite-Group =
    is-closed-under-multiplication-Decidable-Subgroup (group-Finite-Group G) H

  is-closed-under-inverses-Subgroup-Finite-Group :
    is-closed-under-inverses-subset-Group
      ( group-Finite-Group G)
      subset-Subgroup-Finite-Group
  is-closed-under-inverses-Subgroup-Finite-Group =
    is-closed-under-inverses-Decidable-Subgroup (group-Finite-Group G) H

is-emb-decidable-subset-Subgroup-Finite-Group :
  {l1 l2 : Level} (G : Finite-Group l1) →
  is-emb (decidable-subset-Subgroup-Finite-Group {l2 = l2} G)
is-emb-decidable-subset-Subgroup-Finite-Group G =
  is-emb-decidable-subset-Decidable-Subgroup (group-Finite-Group G)
```

### The underlying group of a decidable subgroup

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  type-group-Subgroup-Finite-Group : UU (l1 ⊔ l2)
  type-group-Subgroup-Finite-Group = type-Subgroup-Finite-Group G H

  map-inclusion-group-Subgroup-Finite-Group :
    type-group-Subgroup-Finite-Group → type-Finite-Group G
  map-inclusion-group-Subgroup-Finite-Group =
    inclusion-Subgroup-Finite-Group G H

  is-emb-inclusion-group-Subgroup-Finite-Group :
    is-emb map-inclusion-group-Subgroup-Finite-Group
  is-emb-inclusion-group-Subgroup-Finite-Group =
    is-emb-inclusion-Subgroup-Finite-Group G H

  eq-subgroup-eq-Finite-Group :
    {x y : type-Subgroup-Finite-Group G H} →
    ( inclusion-Subgroup-Finite-Group G H x ＝
      inclusion-Subgroup-Finite-Group G H y) →
    x ＝ y
  eq-subgroup-eq-Finite-Group =
    eq-decidable-subgroup-eq-group (group-Finite-Group G) H

  set-group-Subgroup-Finite-Group : Set (l1 ⊔ l2)
  set-group-Subgroup-Finite-Group =
    set-group-Decidable-Subgroup (group-Finite-Group G) H

  mul-Subgroup-Finite-Group :
    (x y : type-Subgroup-Finite-Group G H) → type-Subgroup-Finite-Group G H
  mul-Subgroup-Finite-Group = mul-Decidable-Subgroup (group-Finite-Group G) H

  associative-mul-Subgroup-Finite-Group :
    (x y z : type-Subgroup-Finite-Group G H) →
    mul-Subgroup-Finite-Group (mul-Subgroup-Finite-Group x y) z ＝
    mul-Subgroup-Finite-Group x (mul-Subgroup-Finite-Group y z)
  associative-mul-Subgroup-Finite-Group =
    associative-mul-Decidable-Subgroup (group-Finite-Group G) H

  unit-Subgroup-Finite-Group : type-Subgroup-Finite-Group G H
  unit-Subgroup-Finite-Group = unit-Decidable-Subgroup (group-Finite-Group G) H

  left-unit-law-mul-Subgroup-Finite-Group :
    (x : type-Subgroup-Finite-Group G H) →
    mul-Subgroup-Finite-Group unit-Subgroup-Finite-Group x ＝ x
  left-unit-law-mul-Subgroup-Finite-Group =
    left-unit-law-mul-Decidable-Subgroup (group-Finite-Group G) H

  right-unit-law-mul-Subgroup-Finite-Group :
    (x : type-Subgroup-Finite-Group G H) →
    mul-Subgroup-Finite-Group x unit-Subgroup-Finite-Group ＝ x
  right-unit-law-mul-Subgroup-Finite-Group =
    right-unit-law-mul-Decidable-Subgroup (group-Finite-Group G) H

  inv-Subgroup-Finite-Group :
    type-Subgroup-Finite-Group G H → type-Subgroup-Finite-Group G H
  inv-Subgroup-Finite-Group = inv-Decidable-Subgroup (group-Finite-Group G) H

  left-inverse-law-mul-Subgroup-Finite-Group :
    ( x : type-Subgroup-Finite-Group G H) →
    mul-Subgroup-Finite-Group (inv-Subgroup-Finite-Group x) x ＝
    unit-Subgroup-Finite-Group
  left-inverse-law-mul-Subgroup-Finite-Group =
    left-inverse-law-mul-Decidable-Subgroup (group-Finite-Group G) H

  right-inverse-law-mul-Subgroup-Finite-Group :
    (x : type-Subgroup-Finite-Group G H) →
    mul-Subgroup-Finite-Group x (inv-Subgroup-Finite-Group x) ＝
    unit-Subgroup-Finite-Group
  right-inverse-law-mul-Subgroup-Finite-Group =
    right-inverse-law-mul-Decidable-Subgroup (group-Finite-Group G) H

  finite-semigroup-Subgroup-Finite-Group : Finite-Semigroup (l1 ⊔ l2)
  pr1 finite-semigroup-Subgroup-Finite-Group =
    finite-type-Subgroup-Finite-Group G H
  pr1 (pr2 finite-semigroup-Subgroup-Finite-Group) = mul-Subgroup-Finite-Group
  pr2 (pr2 finite-semigroup-Subgroup-Finite-Group) =
    associative-mul-Subgroup-Finite-Group

  finite-group-Subgroup-Finite-Group : Finite-Group (l1 ⊔ l2)
  pr1 finite-group-Subgroup-Finite-Group =
    finite-semigroup-Subgroup-Finite-Group
  pr1 (pr1 (pr2 finite-group-Subgroup-Finite-Group)) =
    unit-Subgroup-Finite-Group
  pr1 (pr2 (pr1 (pr2 finite-group-Subgroup-Finite-Group))) =
    left-unit-law-mul-Subgroup-Finite-Group
  pr2 (pr2 (pr1 (pr2 finite-group-Subgroup-Finite-Group))) =
    right-unit-law-mul-Subgroup-Finite-Group
  pr1 (pr2 (pr2 finite-group-Subgroup-Finite-Group)) = inv-Subgroup-Finite-Group
  pr1 (pr2 (pr2 (pr2 finite-group-Subgroup-Finite-Group))) =
    left-inverse-law-mul-Subgroup-Finite-Group
  pr2 (pr2 (pr2 (pr2 finite-group-Subgroup-Finite-Group))) =
    right-inverse-law-mul-Subgroup-Finite-Group

semigroup-Subgroup-Finite-Group :
  {l1 l2 : Level} (G : Finite-Group l1) →
  Subgroup-Finite-Group l2 G →
  Semigroup (l1 ⊔ l2)
semigroup-Subgroup-Finite-Group G H =
  semigroup-Finite-Semigroup (finite-semigroup-Subgroup-Finite-Group G H)

group-Subgroup-Finite-Group :
  {l1 l2 : Level} (G : Finite-Group l1) →
  Subgroup-Finite-Group l2 G →
  Group (l1 ⊔ l2)
group-Subgroup-Finite-Group G H =
  group-Finite-Group (finite-group-Subgroup-Finite-Group G H)
```

### The inclusion homomorphism of the underlying finite group of a finite subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  preserves-mul-inclusion-group-Subgroup-Finite-Group :
    preserves-mul-Group
      ( group-Subgroup-Finite-Group G H)
      ( group-Finite-Group G)
      ( inclusion-Subgroup-Finite-Group G H)
  preserves-mul-inclusion-group-Subgroup-Finite-Group {x} {y} =
    preserves-mul-inclusion-Decidable-Subgroup (group-Finite-Group G) H {x} {y}

  preserves-unit-inclusion-group-Subgroup-Finite-Group :
    preserves-unit-Group
      ( group-Subgroup-Finite-Group G H)
      ( group-Finite-Group G)
      ( inclusion-Subgroup-Finite-Group G H)
  preserves-unit-inclusion-group-Subgroup-Finite-Group =
    preserves-unit-inclusion-Decidable-Subgroup (group-Finite-Group G) H

  preserves-inverses-inclusion-group-Subgroup-Finite-Group :
    preserves-inverses-Group
      ( group-Subgroup-Finite-Group G H)
      ( group-Finite-Group G)
      ( inclusion-Subgroup-Finite-Group G H)
  preserves-inverses-inclusion-group-Subgroup-Finite-Group {x} =
    preserves-inverses-inclusion-Decidable-Subgroup (group-Finite-Group G) H {x}

  inclusion-group-Subgroup-Finite-Group :
    hom-Group (group-Subgroup-Finite-Group G H) (group-Finite-Group G)
  inclusion-group-Subgroup-Finite-Group =
    hom-inclusion-Decidable-Subgroup (group-Finite-Group G) H
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  has-same-elements-Subgroup-Finite-Group :
    {l3 : Level} → Subgroup-Finite-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup-Finite-Group =
    has-same-elements-Decidable-Subgroup (group-Finite-Group G) H

  extensionality-Subgroup-Finite-Group :
    (K : Subgroup-Finite-Group l2 G) →
    (H ＝ K) ≃ has-same-elements-Subgroup-Finite-Group K
  extensionality-Subgroup-Finite-Group =
    extensionality-Decidable-Subgroup (group-Finite-Group G) H
```

### Every finite subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  right-sim-Subgroup-Finite-Group : (x y : type-Finite-Group G) → UU l2
  right-sim-Subgroup-Finite-Group =
    right-sim-Decidable-Subgroup (group-Finite-Group G) H

  is-prop-right-sim-Subgroup-Finite-Group :
    (x y : type-Finite-Group G) → is-prop (right-sim-Subgroup-Finite-Group x y)
  is-prop-right-sim-Subgroup-Finite-Group =
    is-prop-right-sim-Decidable-Subgroup (group-Finite-Group G) H

  prop-right-equivalence-relation-Subgroup-Finite-Group :
    (x y : type-Finite-Group G) → Prop l2
  prop-right-equivalence-relation-Subgroup-Finite-Group =
    prop-right-equivalence-relation-Decidable-Subgroup (group-Finite-Group G) H

  refl-right-sim-Subgroup-Finite-Group :
    is-reflexive right-sim-Subgroup-Finite-Group
  refl-right-sim-Subgroup-Finite-Group =
    refl-right-sim-Decidable-Subgroup (group-Finite-Group G) H

  symmetric-right-sim-Subgroup-Finite-Group :
    is-symmetric right-sim-Subgroup-Finite-Group
  symmetric-right-sim-Subgroup-Finite-Group =
    symmetric-right-sim-Decidable-Subgroup (group-Finite-Group G) H

  transitive-right-sim-Subgroup-Finite-Group :
    is-transitive right-sim-Subgroup-Finite-Group
  transitive-right-sim-Subgroup-Finite-Group =
    transitive-right-sim-Decidable-Subgroup (group-Finite-Group G) H

  right-equivalence-relation-Subgroup-Finite-Group :
    equivalence-relation l2 (type-Finite-Group G)
  right-equivalence-relation-Subgroup-Finite-Group =
    right-equivalence-relation-Decidable-Subgroup (group-Finite-Group G) H
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`

```agda
module _
  {l1 l2 : Level} (G : Finite-Group l1) (H : Subgroup-Finite-Group l2 G)
  where

  left-sim-Subgroup-Finite-Group : (x y : type-Finite-Group G) → UU l2
  left-sim-Subgroup-Finite-Group =
    left-sim-Decidable-Subgroup (group-Finite-Group G) H

  is-prop-left-sim-Subgroup-Finite-Group :
    (x y : type-Finite-Group G) → is-prop (left-sim-Subgroup-Finite-Group x y)
  is-prop-left-sim-Subgroup-Finite-Group =
    is-prop-left-sim-Decidable-Subgroup (group-Finite-Group G) H

  prop-left-equivalence-relation-Subgroup-Finite-Group :
    (x y : type-Finite-Group G) → Prop l2
  prop-left-equivalence-relation-Subgroup-Finite-Group =
    prop-left-equivalence-relation-Decidable-Subgroup (group-Finite-Group G) H

  refl-left-sim-Subgroup-Finite-Group :
    is-reflexive left-sim-Subgroup-Finite-Group
  refl-left-sim-Subgroup-Finite-Group =
    refl-left-sim-Decidable-Subgroup (group-Finite-Group G) H

  symmetric-left-sim-Subgroup-Finite-Group :
    is-symmetric left-sim-Subgroup-Finite-Group
  symmetric-left-sim-Subgroup-Finite-Group =
    symmetric-left-sim-Decidable-Subgroup (group-Finite-Group G) H

  transitive-left-sim-Subgroup-Finite-Group :
    is-transitive left-sim-Subgroup-Finite-Group
  transitive-left-sim-Subgroup-Finite-Group =
    transitive-left-sim-Decidable-Subgroup (group-Finite-Group G) H

  left-equivalence-relation-Subgroup-Finite-Group :
    equivalence-relation l2 (type-Finite-Group G)
  left-equivalence-relation-Subgroup-Finite-Group =
    left-equivalence-relation-Decidable-Subgroup (group-Finite-Group G) H
```
