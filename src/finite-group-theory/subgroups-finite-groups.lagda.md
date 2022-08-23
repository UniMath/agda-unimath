---
title: Subgroups of finite groups
---

```agda
module finite-group-theory.subgroups-finite-groups where

open import finite-group-theory.finite-groups

open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.decidable-subgroups
open import group-theory.subgroups
```

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

  contains-unit-decidable-subset-finite-group-Prop : UU-Prop l2
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

  is-closed-under-mul-decidable-subset-finite-group-Prop : UU-Prop (l1 ⊔ l2)
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

  is-closed-under-inv-decidable-subset-finite-group-Prop : UU-Prop (l1 ⊔ l2)
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

  is-subgroup-decidable-subset-finite-group-Prop : UU-Prop (l1 ⊔ l2)
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
    
-- Decidable-Subgroup :
--   (l : Level) {l1 : Level} (G : Group-𝔽 l1) → UU ((lsuc l) ⊔ l1)
-- Decidable-Subgroup l G =
--   type-subtype (is-subgroup-decidable-subset-group-Prop {l2 = l} G)

-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where

--   decidable-subset-Decidable-Subgroup : decidable-subset-Group-𝔽 l2 G
--   decidable-subset-Decidable-Subgroup =
--     inclusion-subtype (is-subgroup-decidable-subset-group-Prop G) H

--   subset-Decidable-Subgroup : subset-Group-𝔽 l2 G
--   subset-Decidable-Subgroup =
--     subtype-decidable-subtype decidable-subset-Decidable-Subgroup

--   is-subgroup-subset-Decidable-Subgroup :
--     is-subgroup-subset-Group-𝔽 G subset-Decidable-Subgroup
--   is-subgroup-subset-Decidable-Subgroup = pr2 H

--   subgroup-Decidable-Subgroup : Subgroup l2 G
--   pr1 subgroup-Decidable-Subgroup = subset-Decidable-Subgroup
--   pr2 subgroup-Decidable-Subgroup = is-subgroup-subset-Decidable-Subgroup

--   type-Decidable-Subgroup : UU (l1 ⊔ l2)
--   type-Decidable-Subgroup =
--     type-Subgroup G subgroup-Decidable-Subgroup

--   inclusion-Decidable-Subgroup : type-Decidable-Subgroup → type-Group-𝔽 G
--   inclusion-Decidable-Subgroup =
--     inclusion-Subgroup G subgroup-Decidable-Subgroup

--   is-emb-inclusion-Decidable-Subgroup : is-emb inclusion-Decidable-Subgroup
--   is-emb-inclusion-Decidable-Subgroup =
--     is-emb-inclusion-Subgroup G subgroup-Decidable-Subgroup

--   emb-inclusion-Decidable-Subgroup : type-Decidable-Subgroup ↪ type-Group-𝔽 G
--   emb-inclusion-Decidable-Subgroup =
--     emb-inclusion-Subgroup G subgroup-Decidable-Subgroup

--   is-in-Decidable-Subgroup : type-Group-𝔽 G → UU l2
--   is-in-Decidable-Subgroup =
--     is-in-Subgroup G subgroup-Decidable-Subgroup

--   is-in-subgroup-inclusion-Decidable-Subgroup :
--     (x : type-Decidable-Subgroup) →
--     is-in-Decidable-Subgroup (inclusion-Decidable-Subgroup x)
--   is-in-subgroup-inclusion-Decidable-Subgroup =
--     is-in-subgroup-inclusion-Subgroup G subgroup-Decidable-Subgroup

--   is-prop-is-in-Decidable-Subgroup :
--     (x : type-Group-𝔽 G) → is-prop (is-in-Decidable-Subgroup x)
--   is-prop-is-in-Decidable-Subgroup =
--     is-prop-is-in-Subgroup G subgroup-Decidable-Subgroup

--   is-subgroup-Decidable-Subgroup :
--     is-subgroup-decidable-subset-Group-𝔽 G decidable-subset-Decidable-Subgroup
--   is-subgroup-Decidable-Subgroup =
--     is-subgroup-Subgroup G subgroup-Decidable-Subgroup

--   contains-unit-Decidable-Subgroup :
--     contains-unit-decidable-subset-Group-𝔽 G decidable-subset-Decidable-Subgroup
--   contains-unit-Decidable-Subgroup =
--     contains-unit-Subgroup G subgroup-Decidable-Subgroup

--   is-closed-under-mul-Decidable-Subgroup :
--     is-closed-under-mul-decidable-subset-Group-𝔽 G
--       decidable-subset-Decidable-Subgroup
--   is-closed-under-mul-Decidable-Subgroup =
--     is-closed-under-mul-Subgroup G subgroup-Decidable-Subgroup

--   is-closed-under-inv-Decidable-Subgroup :
--     is-closed-under-inv-decidable-subset-Group-𝔽 G
--       decidable-subset-Decidable-Subgroup
--   is-closed-under-inv-Decidable-Subgroup =
--     is-closed-under-inv-Subgroup G subgroup-Decidable-Subgroup

-- is-emb-decidable-subset-Decidable-Subgroup :
--   {l1 l2 : Level} (G : Group-𝔽 l1) →
--     is-emb (decidable-subset-Decidable-Subgroup {l2 = l2} G)
-- is-emb-decidable-subset-Decidable-Subgroup G =
--   is-emb-inclusion-subtype (is-subgroup-decidable-subset-group-Prop G)
-- ```

-- ### The underlying group of a decidable subgroup

-- ```agda
-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where
  
--   type-group-Decidable-Subgroup :  UU (l1 ⊔ l2)
--   type-group-Decidable-Subgroup =
--     type-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   map-inclusion-group-Decidable-Subgroup :
--     type-group-Decidable-Subgroup → type-Group-𝔽 G
--   map-inclusion-group-Decidable-Subgroup =
--     map-inclusion-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   is-emb-inclusion-group-Decidable-Subgroup :
--     is-emb map-inclusion-group-Decidable-Subgroup
--   is-emb-inclusion-group-Decidable-Subgroup =
--     is-emb-inclusion-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   eq-decidable-subgroup-eq-group :
--     {x y : type-group-Decidable-Subgroup} →
--     ( map-inclusion-group-Decidable-Subgroup x ＝
--       map-inclusion-group-Decidable-Subgroup y) →
--     x ＝ y
--   eq-decidable-subgroup-eq-group =
--     eq-subgroup-eq-group G (subgroup-Decidable-Subgroup G H)

--   set-group-Decidable-Subgroup : UU-Set (l1 ⊔ l2)
--   set-group-Decidable-Subgroup =
--     set-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   mul-Decidable-Subgroup :
--     (x y : type-group-Decidable-Subgroup) → type-group-Decidable-Subgroup
--   mul-Decidable-Subgroup = mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   associative-mul-Decidable-Subgroup :
--     (x y z : type-group-Decidable-Subgroup) →
--     Id (mul-Decidable-Subgroup (mul-Decidable-Subgroup x y) z)
--        (mul-Decidable-Subgroup x (mul-Decidable-Subgroup y z))
--   associative-mul-Decidable-Subgroup =
--     associative-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   unit-Decidable-Subgroup : type-group-Decidable-Subgroup
--   unit-Decidable-Subgroup = unit-Subgroup G (subgroup-Decidable-Subgroup G H)

--   left-unit-law-mul-Decidable-Subgroup :
--     (x : type-group-Decidable-Subgroup) →
--     Id (mul-Decidable-Subgroup unit-Decidable-Subgroup x) x
--   left-unit-law-mul-Decidable-Subgroup =
--     left-unit-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   right-unit-law-mul-Decidable-Subgroup :
--     (x : type-group-Decidable-Subgroup) →
--     Id (mul-Decidable-Subgroup x unit-Decidable-Subgroup) x
--   right-unit-law-mul-Decidable-Subgroup =
--     right-unit-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   inv-Decidable-Subgroup :
--     type-group-Decidable-Subgroup → type-group-Decidable-Subgroup
--   inv-Decidable-Subgroup = inv-Subgroup G (subgroup-Decidable-Subgroup G H)

--   left-inverse-law-mul-Decidable-Subgroup :
--     ( x : type-group-Decidable-Subgroup) →
--     Id ( mul-Decidable-Subgroup (inv-Decidable-Subgroup x) x)
--        ( unit-Decidable-Subgroup)
--   left-inverse-law-mul-Decidable-Subgroup =
--     left-inverse-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   right-inverse-law-mul-Decidable-Subgroup :
--     (x : type-group-Decidable-Subgroup) →
--     Id ( mul-Decidable-Subgroup x (inv-Decidable-Subgroup x))
--        ( unit-Decidable-Subgroup)
--   right-inverse-law-mul-Decidable-Subgroup =
--     right-inverse-law-mul-Subgroup G (subgroup-Decidable-Subgroup G H)

--   semigroup-Decidable-Subgroup : Semigroup (l1 ⊔ l2)
--   semigroup-Decidable-Subgroup =
--     semigroup-Subgroup G (subgroup-Decidable-Subgroup G H)

--   group-Decidable-Subgroup : Group-𝔽 (l1 ⊔ l2)
--   group-Decidable-Subgroup = group-Subgroup G (subgroup-Decidable-Subgroup G H)
-- ```

-- ### The inclusion of the underlying group of a subgroup into the ambient group

-- ```agda
-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where
  
--   preserves-mul-inclusion-group-Decidable-Subgroup :
--     preserves-mul-Group-𝔽
--       ( group-Decidable-Subgroup G H)
--       ( G)
--       ( map-inclusion-group-Decidable-Subgroup G H)
--   preserves-mul-inclusion-group-Decidable-Subgroup =
--     preserves-mul-inclusion-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   preserves-unit-inclusion-group-Decidable-Subgroup :
--     preserves-unit-Group-𝔽
--       ( group-Decidable-Subgroup G H)
--       ( G)
--       ( map-inclusion-group-Decidable-Subgroup G H)
--   preserves-unit-inclusion-group-Decidable-Subgroup =
--     preserves-unit-inclusion-group-Subgroup G (subgroup-Decidable-Subgroup G H)

--   preserves-inverses-inclusion-group-Decidable-Subgroup :
--     preserves-inverses-Group-𝔽
--       ( group-Decidable-Subgroup G H)
--       ( G)
--       ( map-inclusion-group-Decidable-Subgroup G H)
--   preserves-inverses-inclusion-group-Decidable-Subgroup =
--     preserves-inverses-inclusion-group-Subgroup G
--       ( subgroup-Decidable-Subgroup G H)

--   inclusion-group-Decidable-Subgroup :
--     type-hom-Group-𝔽 (group-Decidable-Subgroup G H) G
--   inclusion-group-Decidable-Subgroup =
--     inclusion-group-Subgroup G (subgroup-Decidable-Subgroup G H)
-- ```

-- ## Properties

-- ### Extensionality of the type of all subgroups

-- ```agda
-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where

--   has-same-elements-Decidable-Subgroup :
--     {l3 : Level} → Decidable-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
--   has-same-elements-Decidable-Subgroup K =
--     has-same-elements-decidable-subtype
--       ( decidable-subset-Decidable-Subgroup G H)
--       ( decidable-subset-Decidable-Subgroup G K)

--   extensionality-Decidable-Subgroup :
--     (K : Decidable-Subgroup l2 G) →
--     (H ＝ K) ≃ has-same-elements-Decidable-Subgroup K
--   extensionality-Decidable-Subgroup =
--     extensionality-type-subtype
--       ( is-subgroup-decidable-subset-group-Prop G)
--       ( is-subgroup-Decidable-Subgroup G H)
--       ( λ x → pair id id)
--       ( extensionality-decidable-subtype
--         ( decidable-subset-Decidable-Subgroup G H))
-- ```

-- ### Every subgroup induces two equivalence relations

-- #### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`.

-- ```agda
-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where
  
--   right-sim-Decidable-Subgroup : (x y : type-Group-𝔽 G) → UU (l1 ⊔ l2)
--   right-sim-Decidable-Subgroup =
--     right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   is-prop-right-sim-Decidable-Subgroup :
--     (x y : type-Group-𝔽 G) → is-prop (right-sim-Decidable-Subgroup x y)
--   is-prop-right-sim-Decidable-Subgroup =
--     is-prop-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   prop-right-eq-rel-Decidable-Subgroup :
--     (x y : type-Group-𝔽 G) → UU-Prop (l1 ⊔ l2)
--   prop-right-eq-rel-Decidable-Subgroup =
--     prop-right-eq-rel-Subgroup G (subgroup-Decidable-Subgroup G H)

--   refl-right-sim-Decidable-Subgroup :
--     is-reflexive-Rel-Prop prop-right-eq-rel-Decidable-Subgroup
--   refl-right-sim-Decidable-Subgroup =
--     refl-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   symm-right-sim-Decidable-Subgroup :
--     is-symmetric-Rel-Prop prop-right-eq-rel-Decidable-Subgroup
--   symm-right-sim-Decidable-Subgroup =
--     symm-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   trans-right-sim-Decidable-Subgroup :
--     is-transitive-Rel-Prop prop-right-eq-rel-Decidable-Subgroup
--   trans-right-sim-Decidable-Subgroup =
--     trans-right-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   right-eq-rel-Decidable-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group-𝔽 G)
--   right-eq-rel-Decidable-Subgroup =
--     right-eq-rel-Subgroup G (subgroup-Decidable-Subgroup G H)
-- ```

-- #### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`.

-- ```agda
-- module _
--   {l1 l2 : Level} (G : Group-𝔽 l1) (H : Decidable-Subgroup l2 G)
--   where
  
--   left-sim-Decidable-Subgroup : (x y : type-Group-𝔽 G) → UU (l1 ⊔ l2)
--   left-sim-Decidable-Subgroup =
--     left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   is-prop-left-sim-Decidable-Subgroup :
--     (x y : type-Group-𝔽 G) → is-prop (left-sim-Decidable-Subgroup x y)
--   is-prop-left-sim-Decidable-Subgroup =
--     is-prop-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   prop-left-eq-rel-Decidable-Subgroup : (x y : type-Group-𝔽 G) → UU-Prop (l1 ⊔ l2)
--   prop-left-eq-rel-Decidable-Subgroup =
--     prop-left-eq-rel-Subgroup G (subgroup-Decidable-Subgroup G H)

--   refl-left-sim-Decidable-Subgroup :
--     is-reflexive-Rel-Prop prop-left-eq-rel-Decidable-Subgroup
--   refl-left-sim-Decidable-Subgroup =
--     refl-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   symm-left-sim-Decidable-Subgroup :
--     is-symmetric-Rel-Prop prop-left-eq-rel-Decidable-Subgroup
--   symm-left-sim-Decidable-Subgroup =
--     symm-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   trans-left-sim-Decidable-Subgroup :
--     is-transitive-Rel-Prop prop-left-eq-rel-Decidable-Subgroup
--   trans-left-sim-Decidable-Subgroup =
--     trans-left-sim-Subgroup G (subgroup-Decidable-Subgroup G H)

--   left-eq-rel-Decidable-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group-𝔽 G)
--   left-eq-rel-Decidable-Subgroup =
--     left-eq-rel-Subgroup G (subgroup-Decidable-Subgroup G H)
-- ```
