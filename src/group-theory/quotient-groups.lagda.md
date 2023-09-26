# Quotient groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.quotient-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-functoriality-set-quotients
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalences
open import foundation.functoriality-set-quotients
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
open import group-theory.semigroups
```

</details>

## Idea

Given a normal subgroup `H` of `G`, the quotient group `q : G → G/H` such that
`H ⊆ ker q`, and such that `q` satisfies the universal group with the property
that any group homomorphism `f : G → K` such that `H ⊆ ker f` extends uniquely
along `q` to a group homomorphism `G/H → K`.

## Definitions

### Group homomorphisms that nullify a normal subgroup, i.e., that contain a normal subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2)
  where

  nullifies-normal-subgroup-prop-hom-Group :
    hom-Group G K → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-prop-hom-Group f H =
    leq-prop-Normal-Subgroup G H (kernel-hom-Group G K f)

  nullifies-normal-subgroup-hom-Group :
    hom-Group G K → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group f H =
    type-Prop (nullifies-normal-subgroup-prop-hom-Group f H)

  nullifying-hom-Group : Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifying-hom-Group H =
    type-subtype (λ f → nullifies-normal-subgroup-prop-hom-Group f H)

  hom-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) →
    nullifying-hom-Group H → hom-Group G K
  hom-nullifying-hom-Group H = pr1

  nullifies-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) (f : nullifying-hom-Group H) →
    nullifies-normal-subgroup-hom-Group
      ( hom-nullifying-hom-Group H f) H
  nullifies-nullifying-hom-Group H = pr2
```

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Group l3) (f : nullifying-hom-Group G K H)
  (L : Group l4) → hom-Group K L → nullifying-hom-Group G L H
pr1 (precomp-nullifying-hom-Group G H K f L g) =
  comp-hom-Group G K L g (hom-nullifying-hom-Group G K H f)
pr2 (precomp-nullifying-hom-Group G H K f L g) h p =
  ( ap
    ( map-hom-Group K L g)
    ( nullifies-nullifying-hom-Group G K H f h p)) ∙
  ( preserves-unit-hom-Group K L g)

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (l : Level) (G : Group l1)
  (H : Normal-Subgroup l2 G) (Q : Group l3)
  (q : nullifying-hom-Group G Q H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
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
  set-quotient-Group =
    quotient-Set (eq-rel-congruence-Normal-Subgroup G H)

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group =
    set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group =
    is-set-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  map-quotient-hom-Group : type-Group G → type-quotient-Group
  map-quotient-hom-Group =
    quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-surjective-map-quotient-hom-Group :
    is-surjective map-quotient-hom-Group
  is-surjective-map-quotient-hom-Group =
    is-surjective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-effective-map-quotient-hom-Group :
    is-effective
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( map-quotient-hom-Group)
  is-effective-map-quotient-hom-Group =
    is-effective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-quotient-hom-Group :
    {x y : type-Group G} →
    map-quotient-hom-Group x ＝ map-quotient-hom-Group y →
    sim-congruence-Normal-Subgroup G H x y
  apply-effectiveness-map-quotient-hom-Group =
    apply-effectiveness-quotient-map
      ( eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-quotient-hom-Group' :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup G H x y →
    map-quotient-hom-Group x ＝ map-quotient-hom-Group y
  apply-effectiveness-map-quotient-hom-Group' =
    apply-effectiveness-quotient-map'
      ( eq-rel-congruence-Normal-Subgroup G H)

  reflecting-map-quotient-hom-Group :
    reflecting-map-Equivalence-Relation
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( type-quotient-Group)
  reflecting-map-quotient-hom-Group =
    reflecting-map-quotient-map
      ( eq-rel-congruence-Normal-Subgroup G H)

  is-set-quotient-set-quotient-Group :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( set-quotient-Group)
      ( reflecting-map-quotient-hom-Group)
  is-set-quotient-set-quotient-Group =
    is-set-quotient-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
```

#### The group structure on the quotient group

```agda
  unit-quotient-Group : type-quotient-Group
  unit-quotient-Group = map-quotient-hom-Group (unit-Group G)

  binary-hom-mul-quotient-Group :
    binary-hom-Equivalence-Relation
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
  pr1 binary-hom-mul-quotient-Group = mul-Group G
  pr2 binary-hom-mul-quotient-Group =
    mul-congruence-Normal-Subgroup G H

  mul-quotient-Group :
    (x y : type-quotient-Group) → type-quotient-Group
  mul-quotient-Group =
    binary-map-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( binary-hom-mul-quotient-Group)

  mul-quotient-Group' :
    (x y : type-quotient-Group) → type-quotient-Group
  mul-quotient-Group' x y = mul-quotient-Group y x

  compute-mul-quotient-Group :
    (x y : type-Group G) →
    mul-quotient-Group
      ( map-quotient-hom-Group x)
      ( map-quotient-hom-Group y) ＝
    map-quotient-hom-Group (mul-Group G x y)
  compute-mul-quotient-Group =
    compute-binary-map-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( binary-hom-mul-quotient-Group)

  hom-inv-quotient-Group :
    hom-Equivalence-Relation
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
  pr1 hom-inv-quotient-Group = inv-Group G
  pr2 hom-inv-quotient-Group = inv-congruence-Normal-Subgroup G H

  inv-quotient-Group : type-quotient-Group → type-quotient-Group
  inv-quotient-Group =
    map-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( hom-inv-quotient-Group)

  compute-inv-quotient-Group :
    (x : type-Group G) →
    inv-quotient-Group (map-quotient-hom-Group x) ＝
    map-quotient-hom-Group (inv-Group G x)
  compute-inv-quotient-Group =
    coherence-square-map-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( hom-inv-quotient-Group)

  left-unit-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    mul-quotient-Group unit-quotient-Group x ＝ x
  left-unit-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group unit-quotient-Group y)
          ( y))
      ( λ x →
        ( compute-mul-quotient-Group (unit-Group G) x) ∙
        ( ap map-quotient-hom-Group (left-unit-law-mul-Group G x)))

  right-unit-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    mul-quotient-Group x unit-quotient-Group ＝ x
  right-unit-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group y unit-quotient-Group)
          ( y))
      ( λ x →
        ( compute-mul-quotient-Group x (unit-Group G)) ∙
        ( ap map-quotient-hom-Group (right-unit-law-mul-Group G x)))

  associative-mul-quotient-Group :
    (x y z : type-quotient-Group) →
    ( mul-quotient-Group (mul-quotient-Group x y) z) ＝
    ( mul-quotient-Group x (mul-quotient-Group y z))
  associative-mul-quotient-Group =
    triple-induction-set-quotient'
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( λ x y z →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group (mul-quotient-Group x y) z)
          ( mul-quotient-Group x (mul-quotient-Group y z)))
      ( λ x y z →
        ( ap
          ( mul-quotient-Group' (map-quotient-hom-Group z))
          ( compute-mul-quotient-Group x y)) ∙
        ( ( compute-mul-quotient-Group (mul-Group G x y) z) ∙
          ( ( ap
              ( map-quotient-hom-Group)
              ( associative-mul-Group G x y z)) ∙
            ( ( inv
                ( compute-mul-quotient-Group x (mul-Group G y z))) ∙
              ( ap
                ( mul-quotient-Group (map-quotient-hom-Group x))
                ( inv (compute-mul-quotient-Group y z)))))))

  left-inverse-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    ( mul-quotient-Group (inv-quotient-Group x) x) ＝
    ( unit-quotient-Group)
  left-inverse-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group (inv-quotient-Group y) y)
          ( unit-quotient-Group))
      ( λ x →
        ( ap
          ( mul-quotient-Group' (map-quotient-hom-Group x))
          ( compute-inv-quotient-Group x)) ∙
        ( ( compute-mul-quotient-Group (inv-Group G x) x) ∙
          ( ap map-quotient-hom-Group
            ( left-inverse-law-mul-Group G x))))

  right-inverse-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    ( mul-quotient-Group x (inv-quotient-Group x)) ＝
    ( unit-quotient-Group)
  right-inverse-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group y (inv-quotient-Group y))
          ( unit-quotient-Group))
      ( λ x →
        ( ap
          ( mul-quotient-Group (map-quotient-hom-Group x))
          ( compute-inv-quotient-Group x)) ∙
        ( ( compute-mul-quotient-Group x (inv-Group G x)) ∙
          ( ap map-quotient-hom-Group
            ( right-inverse-law-mul-Group G x))))

  semigroup-quotient-Group : Semigroup (l1 ⊔ l2)
  pr1 semigroup-quotient-Group = set-quotient-Group
  pr1 (pr2 semigroup-quotient-Group) = mul-quotient-Group
  pr2 (pr2 semigroup-quotient-Group) = associative-mul-quotient-Group

  quotient-Group : Group (l1 ⊔ l2)
  pr1 quotient-Group = semigroup-quotient-Group
  pr1 (pr1 (pr2 quotient-Group)) = unit-quotient-Group
  pr1 (pr2 (pr1 (pr2 quotient-Group))) =
    left-unit-law-mul-quotient-Group
  pr2 (pr2 (pr1 (pr2 quotient-Group))) =
    right-unit-law-mul-quotient-Group
  pr1 (pr2 (pr2 quotient-Group)) = inv-quotient-Group
  pr1 (pr2 (pr2 (pr2 quotient-Group))) =
    left-inverse-law-mul-quotient-Group
  pr2 (pr2 (pr2 (pr2 quotient-Group))) =
    right-inverse-law-mul-quotient-Group
```

### The quotient homomorphism into the quotient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  preserves-mul-quotient-hom-Group :
    (x y : type-Group G) →
    map-quotient-hom-Group G N (mul-Group G x y) ＝
    mul-quotient-Group G N
      ( map-quotient-hom-Group G N x)
      ( map-quotient-hom-Group G N y)
  preserves-mul-quotient-hom-Group x y =
    inv (compute-mul-quotient-Group G N x y)

  preserves-unit-quotient-hom-Group :
    map-quotient-hom-Group G N (unit-Group G) ＝ unit-quotient-Group G N
  preserves-unit-quotient-hom-Group = refl

  preserves-inv-quotient-hom-Group :
    (x : type-Group G) →
    map-quotient-hom-Group G N (inv-Group G x) ＝
    inv-quotient-Group G N (map-quotient-hom-Group G N x)
  preserves-inv-quotient-hom-Group x =
    inv (compute-inv-quotient-Group G N x)

  quotient-hom-Group : hom-Group G (quotient-Group G N)
  pr1 quotient-hom-Group = map-quotient-hom-Group G N
  pr2 quotient-hom-Group = preserves-mul-quotient-hom-Group
```

## Properties

### An element is in a normal subgroup `N` if and only if it is in the kernel of the quotient group homomorphism `G → G/N`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup :
      {x : type-Group G} → is-in-Normal-Subgroup G N x →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup n =
      apply-effectiveness-map-quotient-hom-Group' G N
        ( unit-congruence-Normal-Subgroup' G N n)

  abstract
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group :
      {x : type-Group G} →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x →
      is-in-Normal-Subgroup G N x
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group {x} H =
      unit-congruence-Normal-Subgroup G N
        ( apply-effectiveness-map-quotient-hom-Group G N H)
```
