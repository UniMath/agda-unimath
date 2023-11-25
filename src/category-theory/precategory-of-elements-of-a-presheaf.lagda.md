# Precategory of elements of a presheaf

```agda
module category-theory.precategory-of-elements-of-a-presheaf where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Let `F : C^op → Set` be a presheaf on a precategory `C`. The category of
elements of `F` consists of:

- objects are pairs `(A , a)` where `A` is an object in `C` and `a : F(A)`
- a morphism from `(A , a)` to `(B , b)` is a morphism `f : hom_C(A, B)` such
  that `a = F(f)(b)`

```agda
module _ {l1 l2 l3} (C : Precategory l1 l2)
  (F : functor-Precategory (opposite-Precategory C) (Set-Precategory l3))
  where

  element-Precategory : Precategory (l1 ⊔ l3) (l2 ⊔ l3)
  pr1 element-Precategory =
    Σ (obj-Precategory C) λ A →
      pr1 (obj-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3) F A)
  pr1 (pr2 element-Precategory) (A , a) (B , b) =
    set-subset
      (hom-set-Precategory C A B)
      λ f →
        Id-Prop
          (obj-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            A)
          a
          (hom-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            f
            b)
  pr1 (pr1 (pr1 (pr2 (pr2 element-Precategory))) (f , p) (g , q)) =
    comp-hom-Precategory C f g
  pr2 (pr1 (pr1 (pr2 (pr2 element-Precategory))) (f , p) (g , q)) =
    q ∙
    (ap (hom-functor-Precategory
          (opposite-Precategory C)
          (Set-Precategory l3)
          F
          g)
        p ∙
    htpy-eq
      (inv
        (preserves-comp-functor-Precategory
          (opposite-Precategory C)
          (Set-Precategory l3)
          F
          g
          f))
      _)
  pr2 (pr1 (pr2 (pr2 element-Precategory))) h g f =
    eq-type-subtype
      (λ f →
        Id-Prop
          (obj-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            _)
          _
          (hom-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            f
            _))
      (associative-comp-hom-Precategory C (pr1 h) (pr1 g) (pr1 f))
  pr1 (pr1 (pr2 (pr2 (pr2 element-Precategory))) x) =
    id-hom-Precategory C
  pr2 (pr1 (pr2 (pr2 (pr2 element-Precategory))) x) =
    inv
      (htpy-eq
        (preserves-id-functor-Precategory
          (opposite-Precategory C)
          (Set-Precategory l3)
          F
          (pr1 x))
        (pr2 x))
  pr1 (pr2 (pr2 (pr2 (pr2 element-Precategory)))) f =
    eq-type-subtype
      (λ f →
        Id-Prop
          (obj-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            _)
          _
          (hom-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            f
            _))
      (left-unit-law-comp-hom-Precategory C (pr1 f))
  pr2 (pr2 (pr2 (pr2 (pr2 element-Precategory)))) f =
    eq-type-subtype
      (λ f →
        Id-Prop
          (obj-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            _)
          _
          (hom-functor-Precategory
            (opposite-Precategory C)
            (Set-Precategory l3)
            F
            f
            _))
      (right-unit-law-comp-hom-Precategory C (pr1 f))
```

### Projection to C is a functor

```agda
module _ {l1 l2 l3} (C : Precategory l1 l2)
  (F : functor-Precategory (opposite-Precategory C) (Set-Precategory l3))
  where

  proj₁-functor-element-Precategory :
    functor-Precategory (element-Precategory C F) C
  pr1 proj₁-functor-element-Precategory = pr1
  pr1 (pr2 proj₁-functor-element-Precategory) f = pr1 f
  pr1 (pr2 (pr2 proj₁-functor-element-Precategory)) g f = refl
  pr2 (pr2 (pr2 proj₁-functor-element-Precategory)) x = refl
```
