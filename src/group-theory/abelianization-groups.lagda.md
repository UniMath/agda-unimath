# Abelianization of groups

```agda
{-# OPTIONS --lossy-unification #-}

open import foundation.function-extensionality-axiom

module
  group-theory.abelianization-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-large-categories funext
open import category-theory.adjunctions-large-precategories funext
open import category-theory.functors-large-categories funext
open import category-theory.functors-large-precategories funext
open import category-theory.natural-transformations-functors-large-categories funext
open import category-theory.natural-transformations-functors-large-precategories funext

open import foundation.commuting-squares-of-maps funext
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.set-quotients funext
open import foundation.sets funext
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import group-theory.abelian-groups funext
open import group-theory.category-of-abelian-groups funext
open import group-theory.category-of-groups funext
open import group-theory.commutator-subgroups funext
open import group-theory.commuting-squares-of-group-homomorphisms funext
open import group-theory.functoriality-quotient-groups funext
open import group-theory.groups funext
open import group-theory.homomorphisms-abelian-groups funext
open import group-theory.homomorphisms-groups funext
open import group-theory.normal-subgroups funext
open import group-theory.nullifying-group-homomorphisms funext
open import group-theory.quotient-groups funext
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

i.e., the abelianization is left adjoint to the inclusion functor from the
[category of abelian groups](group-theory.category-of-abelian-groups.md) into
the [category of groups](group-theory.category-of-groups.md).

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
abelianization-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  hom-Ab (abelianization-Group G) (abelianization-Group H)
abelianization-hom-Group G H f =
  hom-quotient-Group G H
    ( commutator-normal-subgroup-Group G)
    ( commutator-normal-subgroup-Group H)
    ( f , preserves-commutator-subgroup-hom-Group G H f)

preserves-id-abelianization-functor-Group :
  {l1 : Level} (G : Group l1) →
  abelianization-hom-Group G G (id-hom-Group G) ＝
  id-hom-Ab (abelianization-Group G)
preserves-id-abelianization-functor-Group G =
  preserves-id-hom-quotient-Group' G
    ( commutator-normal-subgroup-Group G)
    ( preserves-commutator-subgroup-hom-Group G G (id-hom-Group G))

preserves-comp-abelianization-functor-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  (g : hom-Group H K) (f : hom-Group G H) →
  abelianization-hom-Group G K (comp-hom-Group G H K g f) ＝
  comp-hom-Ab
    ( abelianization-Group G)
    ( abelianization-Group H)
    ( abelianization-Group K)
    ( abelianization-hom-Group H K g)
    ( abelianization-hom-Group G H f)
preserves-comp-abelianization-functor-Group G H K g f =
  preserves-comp-hom-quotient-Group' G H K
    ( commutator-normal-subgroup-Group G)
    ( commutator-normal-subgroup-Group H)
    ( commutator-normal-subgroup-Group K)
    ( g , preserves-commutator-subgroup-hom-Group H K g)
    ( f , preserves-commutator-subgroup-hom-Group G H f)
    ( preserves-commutator-subgroup-hom-Group G K (comp-hom-Group G H K g f))

abelianization-functor-Group :
  functor-Large-Category id Group-Large-Category Ab-Large-Category
obj-functor-Large-Precategory
  abelianization-functor-Group =
  abelianization-Group
hom-functor-Large-Precategory
  abelianization-functor-Group {l1} {l2} {G} {H} =
  abelianization-hom-Group G H
preserves-comp-functor-Large-Precategory
  abelianization-functor-Group {l1} {l2} {l3} {G} {H} {K} =
  preserves-comp-abelianization-functor-Group G H K
preserves-id-functor-Large-Precategory
  abelianization-functor-Group {l1} {G} =
  preserves-id-abelianization-functor-Group G
```

### The unit of the abelianization adjunction

```agda
hom-unit-abelianization-Group :
  {l1 : Level} (G : Group l1) → hom-Group G (group-abelianization-Group G)
hom-unit-abelianization-Group G =
  quotient-hom-Group G (commutator-normal-subgroup-Group G)

naturality-unit-abelianization-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  coherence-square-hom-Group G H
    ( group-abelianization-Group G)
    ( group-abelianization-Group H)
    ( f)
    ( hom-unit-abelianization-Group G)
    ( hom-unit-abelianization-Group H)
    ( abelianization-hom-Group G H f)
naturality-unit-abelianization-Group G H f =
  naturality-hom-quotient-Group G H
    ( commutator-normal-subgroup-Group G)
    ( commutator-normal-subgroup-Group H)
    ( f , preserves-commutator-subgroup-hom-Group G H f)

naturality-unit-abelianization-Group' :
  naturality-family-of-morphisms-functor-Large-Category
    ( Group-Large-Category)
    ( Group-Large-Category)
    ( id-functor-Large-Category Group-Large-Category)
    ( comp-functor-Large-Category
      ( Group-Large-Category)
      ( Ab-Large-Category)
      ( Group-Large-Category)
      ( forgetful-functor-Ab)
      ( abelianization-functor-Group))
    ( hom-unit-abelianization-Group)
naturality-unit-abelianization-Group' {X = G} {H} f =
  eq-htpy-hom-Group G
    ( group-abelianization-Group H)
    ( naturality-unit-abelianization-Group G H f)

unit-abelianization-Group :
  natural-transformation-Large-Category
    ( Group-Large-Category)
    ( Group-Large-Category)
    ( id-functor-Large-Category Group-Large-Category)
    ( comp-functor-Large-Category
      ( Group-Large-Category)
      ( Ab-Large-Category)
      ( Group-Large-Category)
      ( forgetful-functor-Ab)
      ( abelianization-functor-Group))

hom-natural-transformation-Large-Precategory
  unit-abelianization-Group =
  hom-unit-abelianization-Group
naturality-natural-transformation-Large-Precategory
  unit-abelianization-Group =
  naturality-unit-abelianization-Group'
```

### The universal property of abelianization

**Proof:** Since the abelianization of `G` is constructed as the quotient group
`G/[G,G]`, we immediately obtain that the precomposition function

```text
  hom-Group Gᵃᵇ H → nullifying-hom-Group G H [G,G]
```

is an equivalence for any group `H`. That is, any group homomorphism `f : G → H`
of which the [kernel](group-theory.kernels-homomorphisms-groups.md) contains the
commutator subgroup `[G,G]` extends uniquely to the abelianization.

Since abelian groups have [trivial](group-theory.trivial-subgroups.md)
commutator subgroups and since the inclusion `f [G,G] ⊆ [H,H]` holds for any
group homomorphism, it follows that any group homomorphism `G → A` into an
abelian group `A` extends uniquely to the abelianization `Gᵃᵇ`. This proves the
claim.

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-quotient-group-abelianization-Group :
    universal-property-quotient-Group G
      ( commutator-normal-subgroup-Group G)
      ( group-abelianization-Group G)
      ( nullifying-quotient-hom-Group G (commutator-normal-subgroup-Group G))
  is-quotient-group-abelianization-Group =
    is-quotient-group-quotient-Group G (commutator-normal-subgroup-Group G)

  is-abelianization-abelianization-Group :
    is-abelianization-Group G
      ( abelianization-Group G)
      ( hom-unit-abelianization-Group G)
  is-abelianization-abelianization-Group A =
    is-equiv-comp
      ( hom-nullifying-hom-Group G
        ( group-Ab A)
        ( commutator-normal-subgroup-Group G))
      ( precomp-nullifying-hom-Group G
        ( commutator-normal-subgroup-Group G)
        ( group-abelianization-Group G)
        ( nullifying-quotient-hom-Group G
          ( commutator-normal-subgroup-Group G))
        ( group-Ab A))
      ( is-quotient-group-abelianization-Group (group-Ab A))
      ( is-equiv-hom-nullifying-hom-group-Ab G A)
```

### The abelianization adjunction

```agda
equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab :
  {l1 l2 : Level} (G : Group l1) (A : Ab l2) →
  hom-Ab (abelianization-Group G) A ≃ hom-Group G (group-Ab A)
pr1 (equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab G A) h =
  comp-hom-Group G
    ( group-abelianization-Group G)
    ( group-Ab A)
    ( h)
    ( hom-unit-abelianization-Group G)
pr2 (equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab G A) =
  is-abelianization-abelianization-Group G A

naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab :
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (A : Ab l3) (B : Ab l4) (g : hom-Ab A B) →
  coherence-square-maps
    ( map-equiv (equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab H A))
    ( λ h →
      comp-hom-Ab
        ( abelianization-Group G)
        ( abelianization-Group H)
        ( B)
        ( comp-hom-Ab (abelianization-Group H) A B g h)
        ( abelianization-hom-Group G H f))
    ( λ h →
      comp-hom-Group G H
        ( group-Ab B)
        ( comp-hom-Group H (group-Ab A) (group-Ab B) g h)
        ( f))
    ( map-equiv (equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab G B))
naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab
  G H f A B g h =
  eq-htpy-hom-Group G
    ( group-Ab B)
    ( ( map-hom-Ab A B g ∘ map-hom-Ab (abelianization-Group H) A h) ·l
      ( naturality-unit-abelianization-Group G H f))

is-adjoint-pair-abelianization-forgetful-functor-Ab :
  is-adjoint-pair-Large-Category
    ( Group-Large-Category)
    ( Ab-Large-Category)
    ( abelianization-functor-Group)
    ( forgetful-functor-Ab)
equiv-is-adjoint-pair-Large-Precategory
  is-adjoint-pair-abelianization-forgetful-functor-Ab G A =
  equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab G A
naturality-equiv-is-adjoint-pair-Large-Precategory
  is-adjoint-pair-abelianization-forgetful-functor-Ab
  { X1 = G}
  { X2 = H}
  { Y1 = A}
  { Y2 = B}
  ( f)
  ( g) =
  naturality-equiv-is-adjoint-pair-abelianization-forgetful-functor-Ab H G f
    A B g

abelianization-adjunction-Group :
  Adjunction-Large-Category
    ( λ l → l)
    ( λ l → l)
    ( Group-Large-Category)
    ( Ab-Large-Category)
left-adjoint-Adjunction-Large-Precategory
  abelianization-adjunction-Group =
  abelianization-functor-Group
right-adjoint-Adjunction-Large-Precategory
  abelianization-adjunction-Group =
  forgetful-functor-Ab
is-adjoint-pair-Adjunction-Large-Precategory
  abelianization-adjunction-Group =
  is-adjoint-pair-abelianization-forgetful-functor-Ab
```

## External links

- [Abelianization](https://groupprops.subwiki.org/wiki/Abelianization) at
  Groupprops
- [Abelianization](https://ncatlab.org/nlab/show/abelianization) at $n$lab
- [Abelianization](https://www.wikidata.org/wiki/Q318598) at Wikidata
- [Abelianization](https://en.wikipedia.org/wiki/Commutator_subgroup#Abelianization)
  at Wikipedia
- [Abelianization](https://mathworld.wolfram.com/Abelianization.html) at Wolfram
  MathWorld
