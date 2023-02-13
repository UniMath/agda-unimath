#  Quotient groups

```agda
module group-theory.quotient-groups where

open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.kernels
open import group-theory.normal-subgroups
```

## Idea

Given a normal subgroup `H` of `G`, the quotient group `q : G → G/H` such that `H ⊆ ker q`, and such that `q` satisfies the universal group with the property that any group homomorphism `f : G → K` such that `H ⊆ ker f` extends uniquely along `q` to a group homomorphism `G/H → K`.

## Definitions

### Group homomorphisms that nullify a normal subgroup, i.e., that contain a normal subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2)
  where
  
  nullifies-normal-subgroup-hom-Group-Prop :
    type-hom-Group G K → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group-Prop f H =
    contains-Normal-Subgroup-Prop G H (kernel-hom-Group G K f)

  nullifies-normal-subgroup-hom-Group :
    type-hom-Group G K → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group f H =
    type-Prop (nullifies-normal-subgroup-hom-Group-Prop f H)

  nullifying-hom-Group : Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifying-hom-Group H =
    type-subtype (λ f → nullifies-normal-subgroup-hom-Group-Prop f H)

  hom-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) → nullifying-hom-Group H → type-hom-Group G K
  hom-nullifying-hom-Group H = pr1

  nullifies-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) (f : nullifying-hom-Group H) →
    nullifies-normal-subgroup-hom-Group (hom-nullifying-hom-Group H f) H
  nullifies-nullifying-hom-Group H = pr2
```

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Group l3) (f : nullifying-hom-Group G K H)
  (L : Group l4) → type-hom-Group K L → nullifying-hom-Group G L H
pr1 (precomp-nullifying-hom-Group G H K f L g) =
  comp-hom-Group G K L g (hom-nullifying-hom-Group G K H f)
pr2 (precomp-nullifying-hom-Group G H K f L g) h p =
  ( ap (map-hom-Group K L g) (nullifies-nullifying-hom-Group G K H f h p)) ∙
  ( preserves-unit-hom-Group K L g)

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (l : Level) (G : Group l1) (H : Normal-Subgroup l2 G)
  (Q : Group l3) (q : nullifying-hom-Group G Q H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Group l G H Q q =
  (K : Group l) → is-equiv (precomp-nullifying-hom-Group G H Q q K)
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  where

  set-quotient-Group : Set (l1 ⊔ l2)
  set-quotient-Group = quotient-Set (eq-rel-congruence-Normal-Subgroup G H)

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group = set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group =
    is-set-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  map-quotient-hom-Group : type-Group G → type-quotient-Group
  map-quotient-hom-Group = quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-surjective-map-quotient-hom-Group : is-surjective map-quotient-hom-Group
  is-surjective-map-quotient-hom-Group =
    is-surjective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-effective-map-quotient-hom-Group :
    is-effective (eq-rel-congruence-Normal-Subgroup G H) map-quotient-hom-Group
  is-effective-map-quotient-hom-Group =
    is-effective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-quotient-hom-Group :
    {x y : type-Group G} →
    map-quotient-hom-Group x ＝ map-quotient-hom-Group y →
    sim-congruence-Normal-Subgroup G H x y
  apply-effectiveness-map-quotient-hom-Group =
    apply-effectiveness-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-quotient-hom-Group' :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup G H x y →
    map-quotient-hom-Group x ＝ map-quotient-hom-Group y
  apply-effectiveness-map-quotient-hom-Group' =
    apply-effectiveness-quotient-map' (eq-rel-congruence-Normal-Subgroup G H)

  reflecting-map-quotient-hom-Group :
    reflecting-map-Eq-Rel
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( type-quotient-Group)
  reflecting-map-quotient-hom-Group =
    reflecting-map-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-set-quotient-set-quotient-Group :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( set-quotient-Group)
      ( reflecting-map-quotient-hom-Group)
  is-set-quotient-set-quotient-Group =
    is-set-quotient-set-quotient (eq-rel-congruence-Normal-Subgroup G H)
```

#### The group structure on the quotient group

```agda
  unit-quotient-Group : type-quotient-Group
  unit-quotient-Group = map-quotient-hom-Group (unit-Group G)

--   mul-quotient-Group : (x y : type-quotient-Group) → type-quotient-Group
--   mul-quotient-Group =
--     map-inv-is-equiv
--       ( is-set-quotient-set-quotient-Group
--         ( hom-Set set-quotient-Group set-quotient-Group))
--       ( ( λ x →
--           map-inv-is-equiv
--             ( is-set-quotient-set-quotient-Group set-quotient-Group)
--             ( ( λ y → map-quotient-hom-Group (mul-Group G x y)) ,
--               ( λ {y} {z} r →
--                 apply-effectiveness-map-quotient-hom-Group'
--                   ( is-congruence-eq-rel-congruence-Normal-Subgroup G H
--                     ( refl-congruence-Normal-Subgroup G H)
--                     ( r))))) ,
--         ( λ {x} {y} r →
--           eq-htpy
--             ( λ z → {!!})))
-- ```
