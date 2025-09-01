# Decidable subgroups of groups

```agda
module group-theory.decidable-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

A decidable subgroup of a group `G` is a subgroup of `G` defined by a decidable
predicate on the type of elements of `G`.

## Definitions

### Decidable subsets of groups

```agda
decidable-subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → UU (lsuc l ⊔ l1)
decidable-subset-Group l G = decidable-subtype l (type-Group G)

is-set-decidable-subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → is-set (decidable-subset-Group l G)
is-set-decidable-subset-Group l G = is-set-decidable-subtype

module _
  {l1 l2 : Level} (G : Group l1) (P : decidable-subset-Group l2 G)
  where

  subset-decidable-subset-Group : subset-Group l2 G
  subset-decidable-subset-Group = subtype-decidable-subtype P
```

### Decidable subgroups of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : decidable-subset-Group l2 G)
  where

  contains-unit-prop-decidable-subset-Group : Prop l2
  contains-unit-prop-decidable-subset-Group =
    contains-unit-prop-subset-Group G (subset-decidable-subset-Group G P)

  contains-unit-decidable-subset-Group : UU l2
  contains-unit-decidable-subset-Group =
    contains-unit-subset-Group G (subset-decidable-subset-Group G P)

  is-prop-contains-unit-decidable-subset-Group :
    is-prop contains-unit-decidable-subset-Group
  is-prop-contains-unit-decidable-subset-Group =
    is-prop-contains-unit-subset-Group G (subset-decidable-subset-Group G P)

  is-closed-under-multiplication-prop-decidable-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-decidable-subset-Group =
    is-closed-under-multiplication-prop-subset-Group G
      ( subset-decidable-subset-Group G P)

  is-closed-under-multiplication-decidable-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-multiplication-decidable-subset-Group =
    is-closed-under-multiplication-subset-Group G
      ( subset-decidable-subset-Group G P)

  is-prop-is-closed-under-multiplication-decidable-subset-Group :
    is-prop is-closed-under-multiplication-decidable-subset-Group
  is-prop-is-closed-under-multiplication-decidable-subset-Group =
    is-prop-is-closed-under-multiplication-subset-Group G
      ( subset-decidable-subset-Group G P)

  is-closed-under-inverses-prop-decidable-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-inverses-prop-decidable-subset-Group =
    is-closed-under-inverses-prop-subset-Group G
      ( subset-decidable-subset-Group G P)

  is-closed-under-inverses-decidable-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-inverses-decidable-subset-Group =
    is-closed-under-inverses-subset-Group G (subset-decidable-subset-Group G P)

  is-prop-is-closed-under-inverses-decidable-subset-Group :
    is-prop is-closed-under-inverses-decidable-subset-Group
  is-prop-is-closed-under-inverses-decidable-subset-Group =
    is-prop-is-closed-under-inverses-subset-Group G
      ( subset-decidable-subset-Group G P)

  is-subgroup-prop-decidable-subset-Group : Prop (l1 ⊔ l2)
  is-subgroup-prop-decidable-subset-Group =
    is-subgroup-prop-subset-Group G (subset-decidable-subset-Group G P)

  is-subgroup-decidable-subset-Group : UU (l1 ⊔ l2)
  is-subgroup-decidable-subset-Group =
    is-subgroup-subset-Group G (subset-decidable-subset-Group G P)

  is-prop-is-subgroup-decidable-subset-Group :
    is-prop is-subgroup-decidable-subset-Group
  is-prop-is-subgroup-decidable-subset-Group =
    is-prop-is-subgroup-subset-Group G (subset-decidable-subset-Group G P)

Decidable-Subgroup :
  (l : Level) {l1 : Level} (G : Group l1) → UU (lsuc l ⊔ l1)
Decidable-Subgroup l G =
  type-subtype (is-subgroup-prop-decidable-subset-Group {l2 = l} G)

module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  decidable-subset-Decidable-Subgroup : decidable-subset-Group l2 G
  decidable-subset-Decidable-Subgroup =
    inclusion-subtype (is-subgroup-prop-decidable-subset-Group G) H

  subset-Decidable-Subgroup : subset-Group l2 G
  subset-Decidable-Subgroup =
    subtype-decidable-subtype decidable-subset-Decidable-Subgroup

  is-subgroup-subset-Decidable-Subgroup :
    is-subgroup-subset-Group G subset-Decidable-Subgroup
  is-subgroup-subset-Decidable-Subgroup = pr2 H

  subgroup-Decidable-Subgroup : Subgroup l2 G
  pr1 subgroup-Decidable-Subgroup = subset-Decidable-Subgroup
  pr2 subgroup-Decidable-Subgroup = is-subgroup-subset-Decidable-Subgroup

  type-Decidable-Subgroup : UU (l1 ⊔ l2)
  type-Decidable-Subgroup =
    type-Subgroup G subgroup-Decidable-Subgroup

  inclusion-Decidable-Subgroup : type-Decidable-Subgroup → type-Group G
  inclusion-Decidable-Subgroup =
    inclusion-Subgroup G subgroup-Decidable-Subgroup

  is-emb-inclusion-Decidable-Subgroup : is-emb inclusion-Decidable-Subgroup
  is-emb-inclusion-Decidable-Subgroup =
    is-emb-inclusion-Subgroup G subgroup-Decidable-Subgroup

  emb-inclusion-Decidable-Subgroup : type-Decidable-Subgroup ↪ type-Group G
  emb-inclusion-Decidable-Subgroup =
    emb-inclusion-Subgroup G subgroup-Decidable-Subgroup

  is-in-Decidable-Subgroup : type-Group G → UU l2
  is-in-Decidable-Subgroup =
    is-in-Subgroup G subgroup-Decidable-Subgroup

  is-in-subgroup-inclusion-Decidable-Subgroup :
    (x : type-Decidable-Subgroup) →
    is-in-Decidable-Subgroup (inclusion-Decidable-Subgroup x)
  is-in-subgroup-inclusion-Decidable-Subgroup =
    is-in-subgroup-inclusion-Subgroup G subgroup-Decidable-Subgroup

  is-prop-is-in-Decidable-Subgroup :
    (x : type-Group G) → is-prop (is-in-Decidable-Subgroup x)
  is-prop-is-in-Decidable-Subgroup =
    is-prop-is-in-Subgroup G subgroup-Decidable-Subgroup

  is-subgroup-Decidable-Subgroup :
    is-subgroup-decidable-subset-Group G decidable-subset-Decidable-Subgroup
  is-subgroup-Decidable-Subgroup =
    is-subgroup-Subgroup G subgroup-Decidable-Subgroup

  contains-unit-Decidable-Subgroup :
    contains-unit-decidable-subset-Group G decidable-subset-Decidable-Subgroup
  contains-unit-Decidable-Subgroup =
    contains-unit-Subgroup G subgroup-Decidable-Subgroup

  is-closed-under-multiplication-Decidable-Subgroup :
    is-closed-under-multiplication-decidable-subset-Group G
      decidable-subset-Decidable-Subgroup
  is-closed-under-multiplication-Decidable-Subgroup =
    is-closed-under-multiplication-Subgroup G subgroup-Decidable-Subgroup

  is-closed-under-inverses-Decidable-Subgroup :
    is-closed-under-inverses-decidable-subset-Group G
      decidable-subset-Decidable-Subgroup
  is-closed-under-inverses-Decidable-Subgroup =
    is-closed-under-inverses-Subgroup G subgroup-Decidable-Subgroup

is-emb-decidable-subset-Decidable-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
    is-emb (decidable-subset-Decidable-Subgroup {l2 = l2} G)
is-emb-decidable-subset-Decidable-Subgroup G =
  is-emb-inclusion-subtype (is-subgroup-prop-decidable-subset-Group G)
```

### The underlying group of a decidable subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  type-group-Decidable-Subgroup : UU (l1 ⊔ l2)
  type-group-Decidable-Subgroup =
    type-group-Subgroup G (subgroup-Decidable-Subgroup G H)

  map-inclusion-Decidable-Subgroup :
    type-group-Decidable-Subgroup → type-Group G
  map-inclusion-Decidable-Subgroup =
    map-inclusion-Subgroup G (subgroup-Decidable-Subgroup G H)

  eq-decidable-subgroup-eq-group :
    {x y : type-group-Decidable-Subgroup} →
    ( map-inclusion-Decidable-Subgroup x ＝
      map-inclusion-Decidable-Subgroup y) →
    x ＝ y
  eq-decidable-subgroup-eq-group =
    eq-subgroup-eq-group G (subgroup-Decidable-Subgroup G H)

  set-group-Decidable-Subgroup : Set (l1 ⊔ l2)
  set-group-Decidable-Subgroup =
    set-group-Subgroup G (subgroup-Decidable-Subgroup G H)

  mul-Decidable-Subgroup :
    (x y : type-group-Decidable-Subgroup) → type-group-Decidable-Subgroup
  mul-Decidable-Subgroup = mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  associative-mul-Decidable-Subgroup :
    (x y z : type-group-Decidable-Subgroup) →
    Id
      ( mul-Decidable-Subgroup (mul-Decidable-Subgroup x y) z)
      ( mul-Decidable-Subgroup x (mul-Decidable-Subgroup y z))
  associative-mul-Decidable-Subgroup =
    associative-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  unit-Decidable-Subgroup : type-group-Decidable-Subgroup
  unit-Decidable-Subgroup = unit-Subgroup G (subgroup-Decidable-Subgroup G H)

  left-unit-law-mul-Decidable-Subgroup :
    (x : type-group-Decidable-Subgroup) →
    mul-Decidable-Subgroup unit-Decidable-Subgroup x ＝ x
  left-unit-law-mul-Decidable-Subgroup =
    left-unit-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  right-unit-law-mul-Decidable-Subgroup :
    (x : type-group-Decidable-Subgroup) →
    mul-Decidable-Subgroup x unit-Decidable-Subgroup ＝ x
  right-unit-law-mul-Decidable-Subgroup =
    right-unit-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  inv-Decidable-Subgroup :
    type-group-Decidable-Subgroup → type-group-Decidable-Subgroup
  inv-Decidable-Subgroup = inv-Subgroup G (subgroup-Decidable-Subgroup G H)

  left-inverse-law-mul-Decidable-Subgroup :
    ( x : type-group-Decidable-Subgroup) →
    Id
      ( mul-Decidable-Subgroup (inv-Decidable-Subgroup x) x)
      ( unit-Decidable-Subgroup)
  left-inverse-law-mul-Decidable-Subgroup =
    left-inverse-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  right-inverse-law-mul-Decidable-Subgroup :
    (x : type-group-Decidable-Subgroup) →
    Id
      ( mul-Decidable-Subgroup x (inv-Decidable-Subgroup x))
      ( unit-Decidable-Subgroup)
  right-inverse-law-mul-Decidable-Subgroup =
    right-inverse-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

  semigroup-Decidable-Subgroup : Semigroup (l1 ⊔ l2)
  semigroup-Decidable-Subgroup =
    semigroup-Subgroup G (subgroup-Decidable-Subgroup G H)

  group-Decidable-Subgroup : Group (l1 ⊔ l2)
  group-Decidable-Subgroup = group-Subgroup G (subgroup-Decidable-Subgroup G H)
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  preserves-mul-inclusion-Decidable-Subgroup :
    preserves-mul-Group
      ( group-Decidable-Subgroup G H)
      ( G)
      ( map-inclusion-Decidable-Subgroup G H)
  preserves-mul-inclusion-Decidable-Subgroup {x} {y} =
    preserves-mul-inclusion-Subgroup G (subgroup-Decidable-Subgroup G H) {x} {y}

  preserves-unit-inclusion-Decidable-Subgroup :
    preserves-unit-Group
      ( group-Decidable-Subgroup G H)
      ( G)
      ( map-inclusion-Decidable-Subgroup G H)
  preserves-unit-inclusion-Decidable-Subgroup =
    preserves-unit-inclusion-Subgroup G (subgroup-Decidable-Subgroup G H)

  preserves-inverses-inclusion-Decidable-Subgroup :
    preserves-inverses-Group
      ( group-Decidable-Subgroup G H)
      ( G)
      ( map-inclusion-Decidable-Subgroup G H)
  preserves-inverses-inclusion-Decidable-Subgroup {x} =
    preserves-inverses-inclusion-Subgroup G
      ( subgroup-Decidable-Subgroup G H)
      { x}

  hom-inclusion-Decidable-Subgroup :
    hom-Group (group-Decidable-Subgroup G H) G
  hom-inclusion-Decidable-Subgroup =
    hom-inclusion-Subgroup G (subgroup-Decidable-Subgroup G H)
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  has-same-elements-Decidable-Subgroup :
    {l3 : Level} → Decidable-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Decidable-Subgroup K =
    has-same-elements-decidable-subtype
      ( decidable-subset-Decidable-Subgroup G H)
      ( decidable-subset-Decidable-Subgroup G K)

  extensionality-Decidable-Subgroup :
    (K : Decidable-Subgroup l2 G) →
    (H ＝ K) ≃ has-same-elements-Decidable-Subgroup K
  extensionality-Decidable-Subgroup =
    extensionality-type-subtype
      ( is-subgroup-prop-decidable-subset-Group G)
      ( is-subgroup-Decidable-Subgroup G H)
      ( λ x → pair id id)
      ( extensionality-decidable-subtype
        ( decidable-subset-Decidable-Subgroup G H))
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  right-sim-Decidable-Subgroup : (x y : type-Group G) → UU l2
  right-sim-Decidable-Subgroup =
    right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  is-prop-right-sim-Decidable-Subgroup :
    (x y : type-Group G) → is-prop (right-sim-Decidable-Subgroup x y)
  is-prop-right-sim-Decidable-Subgroup =
    is-prop-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  prop-right-equivalence-relation-Decidable-Subgroup :
    (x y : type-Group G) → Prop l2
  prop-right-equivalence-relation-Decidable-Subgroup =
    prop-right-equivalence-relation-Subgroup G (subgroup-Decidable-Subgroup G H)

  refl-right-sim-Decidable-Subgroup :
    is-reflexive right-sim-Decidable-Subgroup
  refl-right-sim-Decidable-Subgroup =
    refl-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  symmetric-right-sim-Decidable-Subgroup :
    is-symmetric right-sim-Decidable-Subgroup
  symmetric-right-sim-Decidable-Subgroup =
    symmetric-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  transitive-right-sim-Decidable-Subgroup :
    is-transitive right-sim-Decidable-Subgroup
  transitive-right-sim-Decidable-Subgroup =
    transitive-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  right-equivalence-relation-Decidable-Subgroup :
    equivalence-relation l2 (type-Group G)
  right-equivalence-relation-Decidable-Subgroup =
    right-equivalence-relation-Subgroup G (subgroup-Decidable-Subgroup G H)
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Decidable-Subgroup l2 G)
  where

  left-sim-Decidable-Subgroup : (x y : type-Group G) → UU l2
  left-sim-Decidable-Subgroup =
    left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  is-prop-left-sim-Decidable-Subgroup :
    (x y : type-Group G) → is-prop (left-sim-Decidable-Subgroup x y)
  is-prop-left-sim-Decidable-Subgroup =
    is-prop-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  prop-left-equivalence-relation-Decidable-Subgroup :
    (x y : type-Group G) → Prop l2
  prop-left-equivalence-relation-Decidable-Subgroup =
    prop-left-equivalence-relation-Subgroup G (subgroup-Decidable-Subgroup G H)

  refl-left-sim-Decidable-Subgroup :
    is-reflexive left-sim-Decidable-Subgroup
  refl-left-sim-Decidable-Subgroup =
    refl-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  symmetric-left-sim-Decidable-Subgroup :
    is-symmetric left-sim-Decidable-Subgroup
  symmetric-left-sim-Decidable-Subgroup =
    symmetric-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  transitive-left-sim-Decidable-Subgroup :
    is-transitive left-sim-Decidable-Subgroup
  transitive-left-sim-Decidable-Subgroup =
    transitive-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

  left-equivalence-relation-Decidable-Subgroup :
    equivalence-relation l2 (type-Group G)
  left-equivalence-relation-Decidable-Subgroup =
    left-equivalence-relation-Subgroup G (subgroup-Decidable-Subgroup G H)
```
