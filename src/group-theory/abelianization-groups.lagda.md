# Abelianization of abstract groups

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module group-theory.abelianization-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-large-categories
open import category-theory.adjunctions-large-precategories
open import category-theory.functors-large-categories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.set-quotients
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.category-of-abelian-groups
open import group-theory.category-of-groups
open import group-theory.commutator-subgroups
open import group-theory.functoriality-quotient-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.quotient-groups
```

</details>

## Idea

Consider a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → A` from a [group](group-theory.groups.md) `G` into an
[abelian group](group-theory.abelian-groups.md) `A`. We say that `f` **is an
abelianization** of `G` if the precomposition function

```text
  - ∘ f : hom A B → hom G B
```

is an [equivalence](foundation-core.equivalences.md) for any abelian group `B`.

The **abelianization** `Gᵃᵇ` of a group `G` always exists, and can be
constructed as the [quotient group](group-theory.quotient-groups.md) `G/[G,G]`
of `G` modulo its [commutator subgroup](group-theory.commutator-subgroups.md).
Therefore we obtain an
[adjunction](category-theory.adjunctions-large-categories.md)

```text
  hom Gᵃᵇ A ≃ hom G A,
```

i.e., the abelianization is left adjoint to the inclusion functor from abelian
groups into groups.

## Definitions

### The predicate of being an abelianization

```agda
module _
  {l1 l2 : Level} (G : Group l1) (A : Ab l2) (f : hom-Group G (group-Ab A))
  where

  is-abelianization-Group : UUω
  is-abelianization-Group =
    {l : Level} (B : Ab l) →
    is-equiv (λ h → comp-hom-Group G (group-Ab A) (group-Ab B) h f)
```

### The abelianization of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  group-abelianization-Group : Group l1
  group-abelianization-Group =
    quotient-Group G (commutator-normal-subgroup-Group G)

  hom-abelianization-Group : hom-Group G group-abelianization-Group
  hom-abelianization-Group =
    quotient-hom-Group G (commutator-normal-subgroup-Group G)

  set-abelianization-Group : Set l1
  set-abelianization-Group = set-Group group-abelianization-Group

  type-abelianization-Group : UU l1
  type-abelianization-Group = type-Group group-abelianization-Group

  zero-abelianization-Group : type-abelianization-Group
  zero-abelianization-Group = unit-Group group-abelianization-Group

  add-abelianization-Group :
    (x y : type-abelianization-Group) → type-abelianization-Group
  add-abelianization-Group = mul-Group group-abelianization-Group

  neg-abelianization-Group :
    type-abelianization-Group → type-abelianization-Group
  neg-abelianization-Group = inv-Group group-abelianization-Group

  associative-add-abelianization-Group :
    (x y z : type-abelianization-Group) →
    add-abelianization-Group (add-abelianization-Group x y) z ＝
    add-abelianization-Group x (add-abelianization-Group y z)
  associative-add-abelianization-Group =
    associative-mul-Group group-abelianization-Group

  left-unit-law-add-abelianization-Group :
    (x : type-abelianization-Group) →
    add-abelianization-Group zero-abelianization-Group x ＝ x
  left-unit-law-add-abelianization-Group =
    left-unit-law-mul-Group group-abelianization-Group

  right-unit-law-add-abelianization-Group :
    (x : type-abelianization-Group) →
    add-abelianization-Group x zero-abelianization-Group ＝ x
  right-unit-law-add-abelianization-Group =
    right-unit-law-mul-Group group-abelianization-Group

  left-inverse-law-add-abelianization-Group :
    (x : type-abelianization-Group) →
    add-abelianization-Group (neg-abelianization-Group x) x ＝
    zero-abelianization-Group
  left-inverse-law-add-abelianization-Group =
    left-inverse-law-mul-Group group-abelianization-Group

  right-inverse-law-add-abelianization-Group :
    (x : type-abelianization-Group) →
    add-abelianization-Group x (neg-abelianization-Group x) ＝
    zero-abelianization-Group
  right-inverse-law-add-abelianization-Group =
    right-inverse-law-mul-Group group-abelianization-Group

  map-abelianization-Group :
    type-Group G → type-abelianization-Group
  map-abelianization-Group =
    map-hom-Group G group-abelianization-Group hom-abelianization-Group

  compute-add-abelianization-Group :
    (x y : type-Group G) →
    add-abelianization-Group
      ( map-abelianization-Group x)
      ( map-abelianization-Group y) ＝
    map-abelianization-Group (mul-Group G x y)
  compute-add-abelianization-Group =
    compute-mul-quotient-Group G (commutator-normal-subgroup-Group G)

  abstract
    commutative-add-abelianization-Group :
      (x y : type-abelianization-Group) →
      add-abelianization-Group x y ＝ add-abelianization-Group y x
    commutative-add-abelianization-Group =
      double-induction-quotient-Group G G
        ( commutator-normal-subgroup-Group G)
        ( commutator-normal-subgroup-Group G)
        ( λ x y → Id-Prop set-abelianization-Group _ _)
        ( λ x y →
          ( compute-add-abelianization-Group x y) ∙
          ( apply-effectiveness-map-quotient-hom-Group' G
            ( commutator-normal-subgroup-Group G)
            ( sim-left-sim-congruence-Normal-Subgroup G
              ( commutator-normal-subgroup-Group G)
              ( mul-Group G x y)
              ( mul-Group G y x)
              ( contains-commutator-commutator-subgroup-Group G x y))) ∙
          ( inv (compute-add-abelianization-Group y x)))

  abelianization-Group : Ab l1
  pr1 abelianization-Group = group-abelianization-Group
  pr2 abelianization-Group = commutative-add-abelianization-Group
```

### The abelianization functor

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  abelianization-hom-Group :
    hom-Ab (abelianization-Group G) (abelianization-Group H)
  abelianization-hom-Group =
    hom-quotient-Group G H
      ( commutator-normal-subgroup-Group G)
      ( commutator-normal-subgroup-Group H)
      {!!}

abelianization-functor-Group :
  functor-Large-Category id Group-Large-Category Ab-Large-Category
abelianization-functor-Group = {!!}
```

### The abelianization adjunction

```agda
abelianization-adjunction-Group :
  Adjunction-Large-Category
    ( λ l → l)
    ( λ l → l)
    ( Group-Large-Category)
    ( Ab-Large-Category)
left-adjoint-Adjunction-Large-Precategory
  abelianization-adjunction-Group =
  abelianization-functor-Group
right-adjoint-Adjunction-Large-Precategory abelianization-adjunction-Group =
  {!!}
is-adjoint-pair-Adjunction-Large-Precategory abelianization-adjunction-Group =
  {!!}
```

## External links

- [Abelianization](https://groupprops.subwiki.org/wiki/Abelianization) at
  Groupprops
- [Abelianization](https://ncatlab.org/nlab/show/abelianization) at nlab
- [Abelianization](https://en.wikipedia.org/wiki/Commutator_subgroup#Abelianization)
  at Wikipedia
- [Abelianization](https://mathworld.wolfram.com/Abelianization.html) at Wolfram
  Mathworld
- [Commutator subgroup](https://www.wikidata.org/entity/Q522216) at Wikidata
