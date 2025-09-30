# Quotients of abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.quotients-abelian-groups where
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
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.nullifying-group-homomorphisms
open import group-theory.quotient-groups
open import group-theory.semigroups
open import group-theory.subgroups-abelian-groups
```

</details>

## Idea

Given a subgroup `B` of an abelian group `A`, the quotient group is an abelian
group `A/B` equipped with a group homomorphism `q : A → A/B` such that
`H ⊆ ker q`, and such that `q` satisfies the universal abelian group with the
property that any group homomorphism `f : A → C` such that `B ⊆ ker f` extends
uniquely along `q` to a group homomorphism `A/B → C`.

## Definitions

### Group homomorphisms that nullify a subgroup, i.e., that contain a subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2)
  where

  nullifies-subgroup-prop-hom-Ab :
    hom-Ab A B → Subgroup-Ab l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-subgroup-prop-hom-Ab f H =
    nullifies-normal-subgroup-prop-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)
      ( normal-subgroup-Subgroup-Ab A H)

  nullifies-normal-subgroup-hom-Ab :
    hom-Ab A B → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
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
    (H : Subgroup-Ab l3 A) → nullifying-hom-Ab H → hom-Ab A B
  hom-nullifying-hom-Ab H =
    hom-nullifying-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( normal-subgroup-Subgroup-Ab A H)

  nullifies-subgroup-nullifying-hom-Ab :
    (H : Subgroup-Ab l3 A) (f : nullifying-hom-Ab H) →
    nullifies-normal-subgroup-hom-Ab
      ( hom-nullifying-hom-Ab H f) H
  nullifies-subgroup-nullifying-hom-Ab H =
    nullifies-normal-subgroup-nullifying-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( normal-subgroup-Subgroup-Ab A H)
```

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Ab :
  {l1 l2 l3 l4 : Level} (A : Ab l1) (H : Subgroup-Ab l2 A)
  (B : Ab l3) (f : nullifying-hom-Ab A B H)
  (C : Ab l4) → hom-Ab B C → nullifying-hom-Ab A C H
precomp-nullifying-hom-Ab A H B f C =
  precomp-nullifying-hom-Group
    ( group-Ab A)
    ( normal-subgroup-Subgroup-Ab A H)
    ( group-Ab B)
    ( f)
    ( group-Ab C)

universal-property-quotient-Ab :
  {l1 l2 l3 : Level} (l : Level) (A : Ab l1)
  (H : Subgroup-Ab l2 A) (B : Ab l3)
  (q : nullifying-hom-Ab A B H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Ab l A H B q =
  (C : Ab l) → is-equiv (precomp-nullifying-hom-Ab A H B q C)
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (H : Subgroup-Ab l2 A)
  where

  set-quotient-Ab : Set (l1 ⊔ l2)
  set-quotient-Ab =
    quotient-Set (equivalence-relation-congruence-Subgroup-Ab A H)

  type-quotient-Ab : UU (l1 ⊔ l2)
  type-quotient-Ab =
    set-quotient (equivalence-relation-congruence-Subgroup-Ab A H)

  is-set-type-quotient-Ab : is-set type-quotient-Ab
  is-set-type-quotient-Ab =
    is-set-set-quotient (equivalence-relation-congruence-Subgroup-Ab A H)

  map-quotient-hom-Ab : type-Ab A → type-quotient-Ab
  map-quotient-hom-Ab =
    quotient-map (equivalence-relation-congruence-Subgroup-Ab A H)

  is-surjective-map-quotient-hom-Ab :
    is-surjective map-quotient-hom-Ab
  is-surjective-map-quotient-hom-Ab =
    is-surjective-quotient-map (equivalence-relation-congruence-Subgroup-Ab A H)

  is-effective-map-quotient-hom-Ab :
    is-effective
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( map-quotient-hom-Ab)
  is-effective-map-quotient-hom-Ab =
    is-effective-quotient-map (equivalence-relation-congruence-Subgroup-Ab A H)

  apply-effectiveness-map-quotient-hom-Ab :
    {x y : type-Ab A} →
    map-quotient-hom-Ab x ＝ map-quotient-hom-Ab y →
    sim-congruence-Subgroup-Ab A H x y
  apply-effectiveness-map-quotient-hom-Ab =
    apply-effectiveness-quotient-map
      ( equivalence-relation-congruence-Subgroup-Ab A H)

  apply-effectiveness-map-quotient-hom-Ab' :
    {x y : type-Ab A} →
    sim-congruence-Subgroup-Ab A H x y →
    map-quotient-hom-Ab x ＝ map-quotient-hom-Ab y
  apply-effectiveness-map-quotient-hom-Ab' =
    apply-effectiveness-quotient-map'
      ( equivalence-relation-congruence-Subgroup-Ab A H)

  reflecting-map-quotient-hom-Ab :
    reflecting-map-equivalence-relation
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( type-quotient-Ab)
  reflecting-map-quotient-hom-Ab =
    reflecting-map-quotient-map
      ( equivalence-relation-congruence-Subgroup-Ab A H)

  is-set-quotient-set-quotient-Ab :
    is-set-quotient
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( set-quotient-Ab)
      ( reflecting-map-quotient-hom-Ab)
  is-set-quotient-set-quotient-Ab =
    is-set-quotient-set-quotient
      ( equivalence-relation-congruence-Subgroup-Ab A H)
```

#### The group structure on the quotient group

```agda
  zero-quotient-Ab : type-quotient-Ab
  zero-quotient-Ab = map-quotient-hom-Ab (zero-Ab A)

  binary-hom-add-quotient-Ab :
    binary-hom-equivalence-relation
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( equivalence-relation-congruence-Subgroup-Ab A H)
  binary-hom-add-quotient-Ab =
    binary-hom-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  add-quotient-Ab :
    (x y : type-quotient-Ab) → type-quotient-Ab
  add-quotient-Ab =
    mul-quotient-Group (group-Ab A) (normal-subgroup-Subgroup-Ab A H)

  add-quotient-Ab' :
    (x y : type-quotient-Ab) → type-quotient-Ab
  add-quotient-Ab' =
    mul-quotient-Group' (group-Ab A) (normal-subgroup-Subgroup-Ab A H)

  compute-add-quotient-Ab :
    (x y : type-Ab A) →
    add-quotient-Ab
      ( map-quotient-hom-Ab x)
      ( map-quotient-hom-Ab y) ＝
    map-quotient-hom-Ab (add-Ab A x y)
  compute-add-quotient-Ab =
    compute-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  hom-neg-quotient-Ab :
    hom-equivalence-relation
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( equivalence-relation-congruence-Subgroup-Ab A H)
  hom-neg-quotient-Ab =
    hom-inv-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  neg-quotient-Ab : type-quotient-Ab → type-quotient-Ab
  neg-quotient-Ab =
    inv-quotient-Group (group-Ab A) (normal-subgroup-Subgroup-Ab A H)

  compute-neg-quotient-Ab :
    (x : type-Ab A) →
    neg-quotient-Ab (map-quotient-hom-Ab x) ＝
    map-quotient-hom-Ab (neg-Ab A x)
  compute-neg-quotient-Ab =
    compute-inv-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  left-unit-law-add-quotient-Ab :
    (x : type-quotient-Ab) → add-quotient-Ab zero-quotient-Ab x ＝ x
  left-unit-law-add-quotient-Ab =
    left-unit-law-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  right-unit-law-add-quotient-Ab :
    (x : type-quotient-Ab) → add-quotient-Ab x zero-quotient-Ab ＝ x
  right-unit-law-add-quotient-Ab =
    right-unit-law-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  associative-add-quotient-Ab :
    (x y z : type-quotient-Ab) →
    add-quotient-Ab (add-quotient-Ab x y) z ＝
    add-quotient-Ab x (add-quotient-Ab y z)
  associative-add-quotient-Ab =
    associative-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  left-inverse-law-add-quotient-Ab :
    (x : type-quotient-Ab) →
    add-quotient-Ab (neg-quotient-Ab x) x ＝ zero-quotient-Ab
  left-inverse-law-add-quotient-Ab =
    left-inverse-law-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  right-inverse-law-add-quotient-Ab :
    (x : type-quotient-Ab) →
    add-quotient-Ab x (neg-quotient-Ab x) ＝ zero-quotient-Ab
  right-inverse-law-add-quotient-Ab =
    right-inverse-law-mul-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  commutative-add-quotient-Ab :
    (x y : type-quotient-Ab) →
    add-quotient-Ab x y ＝ add-quotient-Ab y x
  commutative-add-quotient-Ab =
    double-induction-set-quotient'
      ( equivalence-relation-congruence-Subgroup-Ab A H)
      ( λ x y →
        Id-Prop
          ( set-quotient-Ab)
          ( add-quotient-Ab x y)
          ( add-quotient-Ab y x))
      ( λ x y →
        ( compute-add-quotient-Ab x y) ∙
        ( ap map-quotient-hom-Ab (commutative-add-Ab A x y)) ∙
        ( inv (compute-add-quotient-Ab y x)))

  semigroup-quotient-Ab : Semigroup (l1 ⊔ l2)
  semigroup-quotient-Ab =
    semigroup-quotient-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A H)

  group-quotient-Ab : Group (l1 ⊔ l2)
  group-quotient-Ab =
    quotient-Group (group-Ab A) (normal-subgroup-Subgroup-Ab A H)

  quotient-Ab : Ab (l1 ⊔ l2)
  pr1 quotient-Ab = group-quotient-Ab
  pr2 quotient-Ab = commutative-add-quotient-Ab
```
