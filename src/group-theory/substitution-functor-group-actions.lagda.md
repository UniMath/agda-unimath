# The substitution functor of group actions

```agda
module group-theory.substitution-functor-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.precategory-of-group-actions
open import group-theory.symmetric-groups
```

</details>

## Idea

Given a [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H`
and an [`H`-set](group-theory.group-actions.md) `Y`, we obtain a `G`-action on
`Y` by `g,x ↦ f(g)x`. This operation is functorial in `Y`.

## Definition

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : hom-Group G H)
  where

  obj-subst-action-Group :
    {l3 : Level} → action-Group H l3 → action-Group G l3
  pr1 (obj-subst-action-Group X) = set-action-Group H X
  pr2 (obj-subst-action-Group X) =
    comp-hom-Group G H
      ( symmetric-Group (set-action-Group H X))
      ( pr2 X)
      ( f)

  hom-subst-action-Group :
    {l3 l4 : Level}
    (X : action-Group H l3) (Y : action-Group H l4) →
    hom-action-Group H X Y →
    hom-action-Group G
      ( obj-subst-action-Group X)
      ( obj-subst-action-Group Y)
  pr1 (hom-subst-action-Group X Y h) = pr1 h
  pr2 (hom-subst-action-Group X Y h) x = pr2 h (map-hom-Group G H f x)

  preserves-id-subst-action-Group :
    {l3 : Level} (X : action-Group H l3) →
    Id
      ( hom-subst-action-Group X X (id-hom-action-Group H X))
      ( id-hom-action-Group G (obj-subst-action-Group X))
  preserves-id-subst-action-Group X = refl

  preserves-comp-subst-action-Group :
    {l3 l4 l5 : Level} (X : action-Group H l3)
    (Y : action-Group H l4) (Z : action-Group H l5)
    (g : hom-action-Group H Y Z)
    (f : hom-action-Group H X Y) →
    Id
      ( hom-subst-action-Group X Z
        ( comp-hom-action-Group H X Y Z g f))
      ( comp-hom-action-Group G
        ( obj-subst-action-Group X)
        ( obj-subst-action-Group Y)
        ( obj-subst-action-Group Z)
        ( hom-subst-action-Group Y Z g)
        ( hom-subst-action-Group X Y f))
  preserves-comp-subst-action-Group X Y Z g f = refl

  subst-action-Group :
    functor-Large-Precategory (λ l → l)
      ( action-Group-Large-Precategory H)
      ( action-Group-Large-Precategory G)
  obj-functor-Large-Precategory subst-action-Group =
    obj-subst-action-Group
  hom-functor-Large-Precategory subst-action-Group {X = X} {Y} =
    hom-subst-action-Group X Y
  preserves-comp-functor-Large-Precategory subst-action-Group
    {l1} {l2} {l3} {X} {Y} {Z} =
    preserves-comp-subst-action-Group X Y Z
  preserves-id-functor-Large-Precategory
    subst-action-Group {l1} {X} =
    preserves-id-subst-action-Group X
```

## Properties

### The substitution functor has a left adjoint

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : hom-Group G H)
  where

  preset-obj-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 → Set (l2 ⊔ l3)
  preset-obj-left-adjoint-subst-action-Group X =
    product-Set (set-Group H) (set-action-Group G X)

  pretype-obj-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 → UU (l2 ⊔ l3)
  pretype-obj-left-adjoint-subst-action-Group X =
    type-Set (preset-obj-left-adjoint-subst-action-Group X)

  is-set-pretype-obj-left-adjoint-subst-action-Group :
    {l3 : Level} (X : action-Group G l3) →
    is-set (pretype-obj-left-adjoint-subst-action-Group X)
  is-set-pretype-obj-left-adjoint-subst-action-Group X =
    is-set-type-Set (preset-obj-left-adjoint-subst-action-Group X)

  equivalence-relation-obj-left-adjoint-subst-action-Group :
    {l3 : Level} (X : action-Group G l3) →
    equivalence-relation
      ( l1 ⊔ l2 ⊔ l3)
      ( pretype-obj-left-adjoint-subst-action-Group X)
  pr1
    ( equivalence-relation-obj-left-adjoint-subst-action-Group X)
    ( h , x)
    ( h' , x') =
    exists-structure-Prop
      ( type-Group G)
      ( λ g →
        ( Id (mul-Group H (map-hom-Group G H f g) h) h') ×
        ( Id (mul-action-Group G X g x) x'))
  pr1
    ( pr2 (equivalence-relation-obj-left-adjoint-subst-action-Group X))
    ( h , x) =
    intro-exists
      ( unit-Group G)
      ( pair
        ( ( ap (mul-Group' H h) (preserves-unit-hom-Group G H f)) ∙
          ( left-unit-law-mul-Group H h))
        ( preserves-unit-mul-action-Group G X x))
  pr1
    ( pr2
      ( pr2
        ( equivalence-relation-obj-left-adjoint-subst-action-Group X)))
    ( h , x)
    ( h' , x')
    ( e) =
    apply-universal-property-trunc-Prop e
      ( pr1
        ( equivalence-relation-obj-left-adjoint-subst-action-Group X)
        ( h' , x')
        ( h , x))
      ( λ (g , p , q) →
        intro-exists
          ( inv-Group G g)
          ( ( ( ap
                ( mul-Group' H h')
                ( preserves-inv-hom-Group G H f)) ∙
              ( inv (transpose-eq-mul-Group' H p))) ,
            ( inv (transpose-eq-mul-action-Group G X g x x' q))))
  pr2
    ( pr2
      ( pr2
        ( equivalence-relation-obj-left-adjoint-subst-action-Group X)))
    ( h , x)
    ( h' , x')
    ( h'' , x'')
    ( d)
    ( e) =
    apply-twice-universal-property-trunc-Prop e d
      ( pr1
        ( equivalence-relation-obj-left-adjoint-subst-action-Group X)
        ( h , x)
        ( h'' , x''))
      ( λ (g , p , q) (g' , p' , q') →
        intro-exists
          ( mul-Group G g' g)
          ( ( ( ap
                ( mul-Group' H h)
                ( preserves-mul-hom-Group G H f)) ∙
              ( associative-mul-Group H
                ( map-hom-Group G H f g')
                ( map-hom-Group G H f g)
                ( h)) ∙
              ( ap (mul-Group H (map-hom-Group G H f g')) p) ∙
              ( p')) ,
            ( ( preserves-mul-action-Group G X g' g x) ∙
              ( ap (mul-action-Group G X g') q) ∙
              ( q'))))

  set-left-adjoint-subst-action-Group :
    {l3 : Level} → action-Group G l3 →
    Set (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  set-left-adjoint-subst-action-Group X =
    equivalence-class-Set
      ( equivalence-relation-obj-left-adjoint-subst-action-Group X)
```
