# Quotients of abelian groups

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module group-theory.quotients-abelian-groups where
```

<details><summary>Imports</summary>
```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.kernels
open import group-theory.quotient-groups
open import group-theory.subgroups-abelian-groups
```
</details>

## Idea

Given a subgroup `B` of an abelian group `A`, the quotient group
is an abelian group `A/B` equipped with a group homomorphism
`q : A → A/B` such that `H ⊆ ker q`, and such that `q` satisfies the
universal abelian group with the property that any group homomorphism
`f : A → C` such that `B ⊆ ker f` extends uniquely along `q` to a
group homomorphism `A/B → C`.

## Definitions

### Group homomorphisms that nullify a subgroup, i.e., that contain a subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2)
  where

  nullifies-subgroup-hom-Ab-Prop :
    type-hom-Ab A B → Subgroup-Ab l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-subgroup-hom-Ab-Prop f H =
    nullifies-normal-subgroup-hom-Group-Prop
      ( group-Ab A)
      ( group-Ab B)
      ( f)
      ( normal-subgroup-Subgroup-Ab A H)

  nullifies-normal-subgroup-hom-Ab :
    type-hom-Ab A B → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Ab f H =
    nullifies-normal-subgroup-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)
      ( normal-subgroup-Subgroup-Ab A H)

  nullifying-hom-Ab : Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
  nullifying-hom-Ab H =
    nullifying-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( normal-subgroup-Subgroup-Ab A H)

  hom-nullifying-hom-Ab :
    (H : Subgroup-Ab l3 A) → nullifying-hom-Ab H → type-hom-Ab A B
  hom-nullifying-hom-Ab H =
    hom-nullifying-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( normal-subgroup-Subgroup-Ab A H)

  nullifies-nullifying-hom-Ab :
    (H : Subgroup-Ab l3 A) (f : nullifying-hom-Ab H) →
    nullifies-normal-subgroup-hom-Ab
      ( hom-nullifying-hom-Ab H f) H
  nullifies-nullifying-hom-Ab H =
    nullifies-nullifying-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( normal-subgroup-Subgroup-Ab A H)
```

### The universal property of quotient groups


precomp-nullifying-hom-Ab :
  {l1 l2 l3 l4 : Level} (A : Ab l1) (H : Subgroup-Ab l2 G)
  (K : Group l3) (f : nullifying-hom-Ab G K H)
  (L : Group l4) → type-hom-Ab K L → nullifying-hom-Ab G L H
pr1 (precomp-nullifying-hom-Ab G H K f L g) =
  comp-hom-Ab G K L g (hom-nullifying-hom-Ab G K H f)
pr2 (precomp-nullifying-hom-Ab G H K f L g) h p =
  ( ap
    ( map-hom-Ab K L g)
    ( nullifies-nullifying-hom-Ab G K H f h p)) ∙
  ( preserves-unit-hom-Ab K L g)

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (l : Level) (A : Ab l1)
  (H : Subgroup-Ab l2 G) (Q : Group l3)
  (q : nullifying-hom-Ab G Q H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Group l G H Q q =
  (K : Group l) → is-equiv (precomp-nullifying-hom-Ab G H Q q K)


### The quotient group

#### The quotient map and the underlying set of the quotient group


module _
  {l1 l2 : Level} (A : Ab l1) (H : Subgroup-Ab l2 G)
  where

  set-quotient-Group : Set (l1 ⊔ l2)
  set-quotient-Group =
    quotient-Set (eq-rel-congruence-Subgroup-Ab G H)

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group =
    set-quotient (eq-rel-congruence-Subgroup-Ab G H)

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group =
    is-set-set-quotient (eq-rel-congruence-Subgroup-Ab G H)

  map-quotient-hom-Ab : type-Group G → type-quotient-Group
  map-quotient-hom-Ab =
    quotient-map (eq-rel-congruence-Subgroup-Ab G H)

  is-surjective-map-quotient-hom-Ab :
    is-surjective map-quotient-hom-Ab
  is-surjective-map-quotient-hom-Ab =
    is-surjective-quotient-map (eq-rel-congruence-Subgroup-Ab G H)

  is-effective-map-quotient-hom-Ab :
    is-effective
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( map-quotient-hom-Ab)
  is-effective-map-quotient-hom-Ab =
    is-effective-quotient-map (eq-rel-congruence-Subgroup-Ab G H)

  apply-effectiveness-map-quotient-hom-Ab :
    {x y : type-Group G} →
    map-quotient-hom-Ab x ＝ map-quotient-hom-Ab y →
    sim-congruence-Subgroup-Ab G H x y
  apply-effectiveness-map-quotient-hom-Ab =
    apply-effectiveness-quotient-map
      ( eq-rel-congruence-Subgroup-Ab G H)

  apply-effectiveness-map-quotient-hom-Ab' :
    {x y : type-Group G} →
    sim-congruence-Subgroup-Ab G H x y →
    map-quotient-hom-Ab x ＝ map-quotient-hom-Ab y
  apply-effectiveness-map-quotient-hom-Ab' =
    apply-effectiveness-quotient-map'
      ( eq-rel-congruence-Subgroup-Ab G H)

  reflecting-map-quotient-hom-Ab :
    reflecting-map-Eq-Rel
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( type-quotient-Group)
  reflecting-map-quotient-hom-Ab =
    reflecting-map-quotient-map
      ( eq-rel-congruence-Subgroup-Ab G H)

  is-set-quotient-set-quotient-Group :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( set-quotient-Group)
      ( reflecting-map-quotient-hom-Ab)
  is-set-quotient-set-quotient-Group =
    is-set-quotient-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)


#### The group structure on the quotient group


  unit-quotient-Group : type-quotient-Group
  unit-quotient-Group = map-quotient-hom-Ab (unit-Group G)

  binary-hom-mul-quotient-Group :
    binary-hom-Eq-Rel
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
  pr1 binary-hom-mul-quotient-Group = mul-Group G
  pr2 binary-hom-mul-quotient-Group =
    mul-congruence-Subgroup-Ab G H

  mul-quotient-Group :
    (x y : type-quotient-Group) → type-quotient-Group
  mul-quotient-Group =
    binary-map-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( binary-hom-mul-quotient-Group)

  mul-quotient-Group' :
    (x y : type-quotient-Group) → type-quotient-Group
  mul-quotient-Group' x y = mul-quotient-Group y x

  compute-mul-quotient-Group :
    (x y : type-Group G) →
    mul-quotient-Group
      ( map-quotient-hom-Ab x)
      ( map-quotient-hom-Ab y) ＝
    map-quotient-hom-Ab (mul-Group G x y)
  compute-mul-quotient-Group =
    compute-binary-map-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( binary-hom-mul-quotient-Group)

  hom-inv-quotient-Group :
    hom-Eq-Rel
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
  pr1 hom-inv-quotient-Group = inv-Group G
  pr2 hom-inv-quotient-Group = inv-congruence-Subgroup-Ab G H

  inv-quotient-Group : type-quotient-Group → type-quotient-Group
  inv-quotient-Group =
    map-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( hom-inv-quotient-Group)

  compute-inv-quotient-Group :
    (x : type-Group G) →
    inv-quotient-Group (map-quotient-hom-Ab x) ＝
    map-quotient-hom-Ab (inv-Group G x)
  compute-inv-quotient-Group =
    coherence-square-map-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( hom-inv-quotient-Group)

  left-unit-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    mul-quotient-Group unit-quotient-Group x ＝ x
  left-unit-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group unit-quotient-Group y)
          ( y))
      ( λ x →
        ( compute-mul-quotient-Group (unit-Group G) x) ∙
        ( ap map-quotient-hom-Ab (left-unit-law-mul-Group G x)))

  right-unit-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    mul-quotient-Group x unit-quotient-Group ＝ x
  right-unit-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group y unit-quotient-Group)
          ( y))
      ( λ x →
        ( compute-mul-quotient-Group x (unit-Group G)) ∙
        ( ap map-quotient-hom-Ab (right-unit-law-mul-Group G x)))

  associative-mul-quotient-Group :
    (x y z : type-quotient-Group) →
    ( mul-quotient-Group (mul-quotient-Group x y) z) ＝
    ( mul-quotient-Group x (mul-quotient-Group y z))
  associative-mul-quotient-Group =
    triple-induction-set-quotient'
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( λ x y z →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group (mul-quotient-Group x y) z)
          ( mul-quotient-Group x (mul-quotient-Group y z)))
      ( λ x y z →
        ( ap
          ( mul-quotient-Group' (map-quotient-hom-Ab z))
          ( compute-mul-quotient-Group x y)) ∙
        ( ( compute-mul-quotient-Group (mul-Group G x y) z) ∙
          ( ( ap
              ( map-quotient-hom-Ab)
              ( associative-mul-Group G x y z)) ∙
            ( ( inv
                ( compute-mul-quotient-Group x (mul-Group G y z))) ∙
              ( ap
                ( mul-quotient-Group (map-quotient-hom-Ab x))
                ( inv (compute-mul-quotient-Group y z)))))))

  left-inverse-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    ( mul-quotient-Group (inv-quotient-Group x) x) ＝
    ( unit-quotient-Group)
  left-inverse-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group (inv-quotient-Group y) y)
          ( unit-quotient-Group))
      ( λ x →
        ( ap
          ( mul-quotient-Group' (map-quotient-hom-Ab x))
          ( compute-inv-quotient-Group x)) ∙
        ( ( compute-mul-quotient-Group (inv-Group G x) x) ∙
          ( ap map-quotient-hom-Ab
            ( left-inverse-law-mul-Group G x))))

  right-inverse-law-mul-quotient-Group :
    (x : type-quotient-Group) →
    ( mul-quotient-Group x (inv-quotient-Group x)) ＝
    ( unit-quotient-Group)
  right-inverse-law-mul-quotient-Group =
    induction-set-quotient
      ( eq-rel-congruence-Subgroup-Ab G H)
      ( λ y →
        Id-Prop
          ( set-quotient-Group)
          ( mul-quotient-Group y (inv-quotient-Group y))
          ( unit-quotient-Group))
      ( λ x →
        ( ap
          ( mul-quotient-Group (map-quotient-hom-Ab x))
          ( compute-inv-quotient-Group x)) ∙
        ( ( compute-mul-quotient-Group x (inv-Group G x)) ∙
          ( ap map-quotient-hom-Ab
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
