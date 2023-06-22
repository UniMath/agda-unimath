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

Given a group homomorphism `f : G → H` and an H-set `Y`, we obtain a G-actio on
`Y` by `g,x ↦ f(g)x`. This operation is functorial in `Y`.

## Definition

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : type-hom-Group G H)
  where

  obj-subst-Abstract-Group-Action :
    {l3 : Level} → Abstract-Group-Action H l3 → Abstract-Group-Action G l3
  pr1 (obj-subst-Abstract-Group-Action X) = set-Abstract-Group-Action H X
  pr2 (obj-subst-Abstract-Group-Action X) =
    comp-hom-Group G H
      ( symmetric-Group (set-Abstract-Group-Action H X))
      ( pr2 X)
      ( f)

  hom-subst-Abstract-Group-Action :
    {l3 l4 : Level}
    (X : Abstract-Group-Action H l3) (Y : Abstract-Group-Action H l4) →
    type-hom-Abstract-Group-Action H X Y →
    type-hom-Abstract-Group-Action G
      ( obj-subst-Abstract-Group-Action X)
      ( obj-subst-Abstract-Group-Action Y)
  pr1 (hom-subst-Abstract-Group-Action X Y h) = pr1 h
  pr2 (hom-subst-Abstract-Group-Action X Y h) x = pr2 h (map-hom-Group G H f x)

  preserves-id-subst-Abstract-Group-Action :
    {l3 : Level} (X : Abstract-Group-Action H l3) →
    Id
      ( hom-subst-Abstract-Group-Action X X (id-hom-Abstract-Group-Action H X))
      ( id-hom-Abstract-Group-Action G (obj-subst-Abstract-Group-Action X))
  preserves-id-subst-Abstract-Group-Action X = refl

  preserves-comp-subst-Abstract-Group-Action :
    {l3 l4 l5 : Level} (X : Abstract-Group-Action H l3)
    (Y : Abstract-Group-Action H l4) (Z : Abstract-Group-Action H l5)
    (g : type-hom-Abstract-Group-Action H Y Z)
    (f : type-hom-Abstract-Group-Action H X Y) →
    Id
      ( hom-subst-Abstract-Group-Action X Z
        ( comp-hom-Abstract-Group-Action H X Y Z g f))
      ( comp-hom-Abstract-Group-Action G
        ( obj-subst-Abstract-Group-Action X)
        ( obj-subst-Abstract-Group-Action Y)
        ( obj-subst-Abstract-Group-Action Z)
        ( hom-subst-Abstract-Group-Action Y Z g)
        ( hom-subst-Abstract-Group-Action X Y f))
  preserves-comp-subst-Abstract-Group-Action X Y Z g f = refl

  subst-Abstract-Group-Action :
    functor-Large-Precategory
      ( Abstract-Group-Action-Large-Precategory H)
      ( Abstract-Group-Action-Large-Precategory G)
      ( λ l → l)
  obj-functor-Large-Precategory subst-Abstract-Group-Action =
    obj-subst-Abstract-Group-Action
  hom-functor-Large-Precategory subst-Abstract-Group-Action {l1} {l2} {X} {Y} =
    hom-subst-Abstract-Group-Action X Y
  preserves-comp-functor-Large-Precategory subst-Abstract-Group-Action
    {l1} {l2} {l3} {X} {Y} {Z} =
    preserves-comp-subst-Abstract-Group-Action X Y Z
  preserves-id-functor-Large-Precategory subst-Abstract-Group-Action {l1} {X} =
    preserves-id-subst-Abstract-Group-Action X
```

## Properties

### The substitution functor has a left adjoint

```agda
module _
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : type-hom-Group G H)
  where

  preset-obj-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} → Abstract-Group-Action G l3 → Set (l2 ⊔ l3)
  preset-obj-left-adjoint-subst-Abstract-Group-Action X =
    prod-Set (set-Group H) (set-Abstract-Group-Action G X)

  pretype-obj-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} → Abstract-Group-Action G l3 → UU (l2 ⊔ l3)
  pretype-obj-left-adjoint-subst-Abstract-Group-Action X =
    type-Set (preset-obj-left-adjoint-subst-Abstract-Group-Action X)

  is-set-pretype-obj-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} (X : Abstract-Group-Action G l3) →
    is-set (pretype-obj-left-adjoint-subst-Abstract-Group-Action X)
  is-set-pretype-obj-left-adjoint-subst-Abstract-Group-Action X =
    is-set-type-Set (preset-obj-left-adjoint-subst-Abstract-Group-Action X)

  Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} (X : Abstract-Group-Action G l3) →
    Equivalence-Relation
      ( l1 ⊔ l2 ⊔ l3)
      ( pretype-obj-left-adjoint-subst-Abstract-Group-Action X)
  pr1
    ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)
    ( h , x)
    ( h' , x') =
    ∃-Prop
      ( type-Group G)
      ( λ g →
        ( Id (mul-Group H (map-hom-Group G H f g) h) h') ×
        ( Id (mul-Abstract-Group-Action G X g x) x'))
  pr1
    ( pr2 (Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X))
    ( h , x) =
    intro-∃
      ( unit-Group G)
      ( pair
        ( ( ap (mul-Group' H h) (preserves-unit-hom-Group G H f)) ∙
          ( left-unit-law-mul-Group H h))
        ( preserves-unit-mul-Abstract-Group-Action G X x))
  pr1
    ( pr2
      ( pr2
        ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)))
    ( h , x) (h' , x') e =
    apply-universal-property-trunc-Prop e
      ( pr1
        ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)
        ( h' , x')
        ( h , x))
      ( λ { (g , p , q) →
            intro-∃
              ( inv-Group G g)
              ( pair
                ( ( ap
                    ( mul-Group' H h')
                    ( preserves-inv-hom-Group G H f g)) ∙
                  ( inv (transpose-eq-mul-Group' H p)))
                ( inv (transpose-eq-mul-Abstract-Group-Action G X g x x' q)))})
  pr2
    ( pr2
      ( pr2
        ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)))
    ( h , x) (h' , x') (h'' , x'') d e =
    apply-universal-property-trunc-Prop e
      ( pr1
        ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)
        ( h , x)
        ( h'' , x''))
      ( λ { (g , p , q) →
            apply-universal-property-trunc-Prop d
              ( pr1
                ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action
                  ( X))
                ( h , x)
                ( h'' , x''))
              ( λ { (g' , p' , q') →
                    intro-∃
                      ( mul-Group G g' g)
                      ( pair
                        ( ( ap
                            ( mul-Group' H h)
                            ( preserves-mul-hom-Group G H f g' g)) ∙
                          ( ( associative-mul-Group H
                              ( map-hom-Group G H f g')
                              ( map-hom-Group G H f g)
                              ( h)) ∙
                            ( ( ap (mul-Group H (map-hom-Group G H f g')) p) ∙
                              ( p'))))
                        ( ( preserves-mul-Abstract-Group-Action G X g' g x) ∙
                          ( ap (mul-Abstract-Group-Action G X g') q ∙ q')))})})

  set-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} → Abstract-Group-Action G l3 →
    Set (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  set-left-adjoint-subst-Abstract-Group-Action X =
    equivalence-class-Set
      ( Equivalence-Relation-obj-left-adjoint-subst-Abstract-Group-Action X)

{-
  obj-left-adjoint-subst-Abstract-Group-Action :
    {l3 : Level} → Abstract-Group-Action G l3 →
    Abstract-Group-Action H (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  pr1 (obj-left-adjoint-subst-Abstract-Group-Action X) =
    set-left-adjoint-subst-Abstract-Group-Action X
  pr1 (pr2 (obj-left-adjoint-subst-Abstract-Group-Action X)) h = {!!}
  pr2 (pr2 (obj-left-adjoint-subst-Abstract-Group-Action X)) = {!!}
-}
```
