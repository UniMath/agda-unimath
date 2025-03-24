# Precategory of elements of a presheaf

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.precategory-of-elements-of-a-presheaf
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.opposite-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.presheaf-categories funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

Let `F : Cᵒᵖ → Set` be a [presheaf](category-theory.presheaf-categories.md) on a
[precategory](category-theory.precategories.md) `C`. The **precategory of
elements** of `F` consists of:

- Objects are [pairs](foundation.dependent-pair-types.md) `(A , a)` where `A` is
  an object in `C` and `a : F A`.
- A morphism from `(A , a)` to `(B , b)` is a morphism `f : hom A B` in the
  precategory `C` equipped with an
  [identification](foundation-core.identity-types.md) `a = F f b`.

## Definitions

```agda
module _
  {l1 l2 l3} (C : Precategory l1 l2) (F : presheaf-Precategory C l3)
  where

  obj-precategory-of-elements-presheaf-Precategory : UU (l1 ⊔ l3)
  obj-precategory-of-elements-presheaf-Precategory =
    Σ (obj-Precategory C) (element-presheaf-Precategory C F)

  hom-set-precategory-of-elements-presheaf-Precategory :
    (A B : obj-precategory-of-elements-presheaf-Precategory) → Set (l2 ⊔ l3)
  hom-set-precategory-of-elements-presheaf-Precategory (A , a) (B , b) =
    set-subset
      ( hom-set-Precategory C A B)
      ( λ f →
        Id-Prop
          ( element-set-presheaf-Precategory C F A)
          ( a)
          ( action-presheaf-Precategory C F f b))

  hom-precategory-of-elements-presheaf-Precategory :
    (A B : obj-precategory-of-elements-presheaf-Precategory) → UU (l2 ⊔ l3)
  hom-precategory-of-elements-presheaf-Precategory A B =
    type-Set (hom-set-precategory-of-elements-presheaf-Precategory A B)

  eq-hom-precategory-of-elements-presheaf-Precategory :
    {X Y : obj-precategory-of-elements-presheaf-Precategory}
    (f g : hom-precategory-of-elements-presheaf-Precategory X Y) →
    (pr1 f ＝ pr1 g) → f ＝ g
  eq-hom-precategory-of-elements-presheaf-Precategory f g =
    eq-type-subtype
      ( λ h →
        Id-Prop
          ( element-set-presheaf-Precategory C F _)
          ( _)
          ( action-presheaf-Precategory C F h _))

  comp-hom-precategory-of-elements-presheaf-Precategory :
    {X Y Z : obj-precategory-of-elements-presheaf-Precategory} →
    hom-precategory-of-elements-presheaf-Precategory Y Z →
    hom-precategory-of-elements-presheaf-Precategory X Y →
    hom-precategory-of-elements-presheaf-Precategory X Z
  comp-hom-precategory-of-elements-presheaf-Precategory
    ( g , q)
    ( f , p) =
    ( comp-hom-Precategory C g f ,
      ( p) ∙
      ( ap (action-presheaf-Precategory C F f) q) ∙
      ( inv (preserves-comp-action-presheaf-Precategory C F g f _)))

  associative-comp-hom-precategory-of-elements-presheaf-Precategory :
    {X Y Z W : obj-precategory-of-elements-presheaf-Precategory} →
    (h : hom-precategory-of-elements-presheaf-Precategory Z W)
    (g : hom-precategory-of-elements-presheaf-Precategory Y Z)
    (f : hom-precategory-of-elements-presheaf-Precategory X Y) →
    comp-hom-precategory-of-elements-presheaf-Precategory
      ( comp-hom-precategory-of-elements-presheaf-Precategory h g)
      ( f) ＝
    comp-hom-precategory-of-elements-presheaf-Precategory
      ( h)
      ( comp-hom-precategory-of-elements-presheaf-Precategory g f)
  associative-comp-hom-precategory-of-elements-presheaf-Precategory h g f =
    eq-hom-precategory-of-elements-presheaf-Precategory
      ( comp-hom-precategory-of-elements-presheaf-Precategory
        ( comp-hom-precategory-of-elements-presheaf-Precategory h g)
        ( f))
      ( comp-hom-precategory-of-elements-presheaf-Precategory
        ( h)
        ( comp-hom-precategory-of-elements-presheaf-Precategory g f))
      ( associative-comp-hom-Precategory C (pr1 h) (pr1 g) (pr1 f))

  id-hom-precategory-of-elements-presheaf-Precategory :
    {X : obj-precategory-of-elements-presheaf-Precategory} →
    hom-precategory-of-elements-presheaf-Precategory X X
  pr1 id-hom-precategory-of-elements-presheaf-Precategory =
    id-hom-Precategory C
  pr2 id-hom-precategory-of-elements-presheaf-Precategory =
    inv (preserves-id-action-presheaf-Precategory C F _)

  left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory :
    {X Y : obj-precategory-of-elements-presheaf-Precategory} →
    (f : hom-precategory-of-elements-presheaf-Precategory X Y) →
    comp-hom-precategory-of-elements-presheaf-Precategory
      ( id-hom-precategory-of-elements-presheaf-Precategory)
      ( f) ＝
    f
  left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory f =
    eq-hom-precategory-of-elements-presheaf-Precategory
      ( comp-hom-precategory-of-elements-presheaf-Precategory
        ( id-hom-precategory-of-elements-presheaf-Precategory)
        ( f))
      ( f)
      ( left-unit-law-comp-hom-Precategory C (pr1 f))

  right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory :
    {X Y : obj-precategory-of-elements-presheaf-Precategory} →
    (f : hom-precategory-of-elements-presheaf-Precategory X Y) →
    comp-hom-precategory-of-elements-presheaf-Precategory
      ( f)
      ( id-hom-precategory-of-elements-presheaf-Precategory) ＝
    f
  right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory f =
    eq-hom-precategory-of-elements-presheaf-Precategory
      ( comp-hom-precategory-of-elements-presheaf-Precategory
        ( f)
        ( id-hom-precategory-of-elements-presheaf-Precategory))
      ( f)
      ( right-unit-law-comp-hom-Precategory C (pr1 f))

  precategory-of-elements-presheaf-Precategory : Precategory (l1 ⊔ l3) (l2 ⊔ l3)
  precategory-of-elements-presheaf-Precategory =
    make-Precategory
      ( obj-precategory-of-elements-presheaf-Precategory)
      ( hom-set-precategory-of-elements-presheaf-Precategory)
      ( comp-hom-precategory-of-elements-presheaf-Precategory)
      ( λ X → id-hom-precategory-of-elements-presheaf-Precategory {X})
      ( associative-comp-hom-precategory-of-elements-presheaf-Precategory)
      ( left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory)
      ( right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategory)
```

### The projection from the category of elements of a presheaf to the base category

```agda
module _ {l1 l2 l3} (C : Precategory l1 l2)
  (F : functor-Precategory (opposite-Precategory C) (Set-Precategory l3))
  where

  proj-functor-precategory-of-elements-presheaf-Precategory :
    functor-Precategory (precategory-of-elements-presheaf-Precategory C F) C
  pr1 proj-functor-precategory-of-elements-presheaf-Precategory X =
    pr1 X
  pr1 (pr2 proj-functor-precategory-of-elements-presheaf-Precategory) f =
    pr1 f
  pr1
    ( pr2
      ( pr2 proj-functor-precategory-of-elements-presheaf-Precategory)) g f =
    refl
  pr2
    ( pr2
      ( pr2 proj-functor-precategory-of-elements-presheaf-Precategory)) x =
    refl
```
