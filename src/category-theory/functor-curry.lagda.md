# The Currying of Functors on a Product Category

```agda
module category-theory.functor-curry where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors
open import category-theory.products-of-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

In the context of sets, currying means that we can view a function
`f : S × T → U` as a function `f : S → (T → U)`. We can view this as a function
`curry : (S × T → U) → (S → T → U)`. In the context of categories, there is a
similar situation: this file constructs the functor between functor categories

```text
curry-functor : [C × D, E] → [C, [D, E]].
```

## Definition

```agda
module CurryFunctor
  {lc₁ lc₂ ld₁ ld₂ le₁ le₂ : Level}
  (C : Precategory lc₁ lc₂)
  (D : Precategory ld₁ ld₂)
  (E : Precategory le₁ le₂) where
  private
    CD = product-Precategory C D
    CDE1 = functor-precategory-Precategory CD E
    DE = functor-precategory-Precategory D E
    CDE2 = functor-precategory-Precategory C DE

  module _
    (F : obj-Precategory CDE1)
    where

    module _
      (c : obj-Precategory C)
      where

      obj-obj-obj-curry-functor : obj-Precategory D → obj-Precategory E
      obj-obj-obj-curry-functor d = obj-functor-Precategory CD E F (c , d)

      hom-obj-obj-curry-functor :
        {d₁ d₂ : obj-Precategory D}
        → hom-Precategory D d₁ d₂
        → hom-Precategory E
          (obj-obj-obj-curry-functor d₁)
          (obj-obj-obj-curry-functor d₂)
      hom-obj-obj-curry-functor f =
        hom-functor-Precategory CD E F (id-hom-Precategory C , f)

      map-obj-obj-curry-functor : map-Precategory D E
      pr1 map-obj-obj-curry-functor = obj-obj-obj-curry-functor
      pr2 map-obj-obj-curry-functor = hom-obj-obj-curry-functor

      opaque
        preserves-comp-obj-obj-curry-functor :
          preserves-comp-hom-map-Precategory D E map-obj-obj-curry-functor
        preserves-comp-obj-obj-curry-functor f g = equational-reasoning
          hom-functor-Precategory CD E F
            (id-hom-Precategory C , comp-hom-Precategory D f g)
          ＝ hom-functor-Precategory CD E F (comp-hom-Precategory CD
              (id-hom-Precategory C , f) (id-hom-Precategory C , g))
            by ap (λ x → hom-functor-Precategory CD E F (x , _)) (inv
              (left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)))
          ＝ comp-hom-Precategory E
              (hom-functor-Precategory CD E F (id-hom-Precategory C , f))
              (hom-functor-Precategory CD E F (id-hom-Precategory C , g))
            by preserves-comp-functor-Precategory CD E F
              (id-hom-Precategory C , f)
              (id-hom-Precategory C , g)

        preserves-id-obj-obj-curry-functor :
          preserves-id-hom-map-Precategory D E map-obj-obj-curry-functor
        preserves-id-obj-obj-curry-functor d =
          preserves-id-functor-Precategory CD E F (c , d)

      obj-obj-curry-functor : obj-Precategory DE
      pr1 obj-obj-curry-functor = obj-obj-obj-curry-functor
      pr1 (pr2 obj-obj-curry-functor) = hom-obj-obj-curry-functor
      pr1 (pr2 (pr2 obj-obj-curry-functor)) =
        preserves-comp-obj-obj-curry-functor
      pr2 (pr2 (pr2 obj-obj-curry-functor)) = preserves-id-obj-obj-curry-functor

    module _
      {c₁ c₂ : obj-Precategory C}
      (f : hom-Precategory C c₁ c₂)
      where

      hom-hom-obj-curry-functor :
        (d : obj-Precategory D)
        → hom-Precategory E
          (obj-obj-obj-curry-functor c₁ d)
          (obj-obj-obj-curry-functor c₂ d)
      hom-hom-obj-curry-functor d =
        hom-functor-Precategory CD E F (f , id-hom-Precategory D)

      opaque
        is-natural-hom-obj-curry-functor :
          is-natural-transformation-Precategory D E
            (obj-obj-curry-functor c₁) (obj-obj-curry-functor c₂)
            hom-hom-obj-curry-functor
        is-natural-hom-obj-curry-functor {d₁} {d₂} g = equational-reasoning
          comp-hom-Precategory E
            (hom-obj-obj-curry-functor c₂ g)
            (hom-hom-obj-curry-functor d₁)
          ＝ hom-functor-Precategory CD E F (comp-hom-Precategory CD
              (id-hom-Precategory C , g)
              (f , id-hom-Precategory D))
            by inv (preserves-comp-functor-Precategory CD E F
              (id-hom-Precategory C , g)
              (f , id-hom-Precategory D))
          ＝ hom-functor-Precategory CD E F (comp-hom-Precategory CD
              (f , id-hom-Precategory D)
              (id-hom-Precategory C , g))
            by ap (hom-functor-Precategory CD E F) (identity-product
              (left-unit-law-comp-hom-Precategory C f
                ∙ inv (right-unit-law-comp-hom-Precategory C f))
              (right-unit-law-comp-hom-Precategory D g
                ∙ inv (left-unit-law-comp-hom-Precategory D g)))
          ＝ comp-hom-Precategory E
              (hom-hom-obj-curry-functor d₂)
              (hom-obj-obj-curry-functor c₁ g)
            by preserves-comp-functor-Precategory CD E F
              (f , id-hom-Precategory D)
              (id-hom-Precategory C , g)

      hom-obj-curry-functor :
        hom-Precategory DE (obj-obj-curry-functor c₁) (obj-obj-curry-functor c₂)
      pr1 hom-obj-curry-functor = hom-hom-obj-curry-functor
      pr2 hom-obj-curry-functor = is-natural-hom-obj-curry-functor

    map-obj-curry-functor : map-Precategory C DE
    pr1 map-obj-curry-functor = obj-obj-curry-functor
    pr2 map-obj-curry-functor = hom-obj-curry-functor

    opaque
      preserves-comp-obj-curry-functor :
        preserves-comp-hom-map-Precategory C DE map-obj-curry-functor
      preserves-comp-obj-curry-functor {c₁} {c₂} {c₃} f g =
        eq-htpy-hom-family-natural-transformation-Precategory
        D E
        (obj-obj-curry-functor c₁) (obj-obj-curry-functor c₃)
        (hom-obj-curry-functor (comp-hom-Precategory C f g))
        (comp-hom-Precategory DE
          {obj-obj-curry-functor c₁}
          {obj-obj-curry-functor c₂}
          {obj-obj-curry-functor c₃}
          (hom-obj-curry-functor f)
          (hom-obj-curry-functor g))
        (λ d → equational-reasoning
          hom-functor-Precategory CD E F
            (comp-hom-Precategory C f g , id-hom-Precategory D)
          ＝ hom-functor-Precategory CD E F (comp-hom-Precategory CD
              (f , id-hom-Precategory D)
              (g , id-hom-Precategory D))
            by ap
              (λ h → hom-functor-Precategory CD E F
                (comp-hom-Precategory C f g , h))
              (inv
                (left-unit-law-comp-hom-Precategory D (id-hom-Precategory D)))
          ＝ comp-hom-Precategory E
              (hom-functor-Precategory CD E F (f , id-hom-Precategory D))
              (hom-functor-Precategory CD E F (g , id-hom-Precategory D))
          by preserves-comp-functor-Precategory CD E F
            (f , id-hom-Precategory D)
            (g , id-hom-Precategory D))

      preserves-id-obj-curry-functor :
        preserves-id-hom-map-Precategory C DE map-obj-curry-functor
      preserves-id-obj-curry-functor c =
        eq-htpy-hom-family-natural-transformation-Precategory
        D E
        (obj-obj-curry-functor c)
        (obj-obj-curry-functor c)
        (hom-obj-curry-functor (id-hom-Precategory C))
        (id-hom-Precategory DE {obj-obj-curry-functor c})
        (λ d → preserves-id-functor-Precategory CD E F (c , d))

    obj-curry-functor : obj-Precategory CDE2
    pr1 obj-curry-functor = obj-obj-curry-functor
    pr1 (pr2 obj-curry-functor) = hom-obj-curry-functor
    pr1 (pr2 (pr2 obj-curry-functor)) = preserves-comp-obj-curry-functor
    pr2 (pr2 (pr2 obj-curry-functor)) = preserves-id-obj-curry-functor

  module _
    {F₁ F₂ : obj-Precategory CDE1}
    (α : hom-Precategory CDE1 F₁ F₂)
    where

    module _
      (c : obj-Precategory C)
      where

      hom-hom-hom-curry-functor :
        (d : obj-Precategory D)
        → hom-Precategory E
          (obj-obj-obj-curry-functor F₁ c d)
          (obj-obj-obj-curry-functor F₂ c d)
      hom-hom-hom-curry-functor d =
        hom-family-natural-transformation-Precategory CD E F₁ F₂ α (c , d)

      opaque
        is-natural-hom-hom-curry-functor :
          is-natural-transformation-Precategory D E
            (obj-obj-curry-functor F₁ c) (obj-obj-curry-functor F₂ c)
            hom-hom-hom-curry-functor
        is-natural-hom-hom-curry-functor {d₁} {d₂} f =
          naturality-natural-transformation-Precategory CD E F₁ F₂ α
          (id-hom-Precategory C , f)

      hom-hom-curry-functor :
        hom-Precategory DE
          (obj-obj-curry-functor F₁ c) (obj-obj-curry-functor F₂ c)
      pr1 hom-hom-curry-functor = hom-hom-hom-curry-functor
      pr2 hom-hom-curry-functor = is-natural-hom-hom-curry-functor

    opaque
      is-natural-hom-curry-functor :
        is-natural-transformation-Precategory C DE
          (obj-curry-functor F₁) (obj-curry-functor F₂)
          hom-hom-curry-functor
      is-natural-hom-curry-functor {c₁} {c₂} f =
        eq-htpy-hom-family-natural-transformation-Precategory
        D E
        (obj-obj-curry-functor F₁ c₁) (obj-obj-curry-functor F₂ c₂)
        (comp-hom-Precategory DE
          {obj-obj-curry-functor F₁ c₁}
          {obj-obj-curry-functor F₂ c₁}
          {obj-obj-curry-functor F₂ c₂}
          (hom-obj-curry-functor F₂ f)
          (hom-hom-curry-functor c₁))
        (comp-hom-Precategory DE
          {obj-obj-curry-functor F₁ c₁}
          {obj-obj-curry-functor F₁ c₂}
          {obj-obj-curry-functor F₂ c₂}
          (hom-hom-curry-functor c₂)
          (hom-obj-curry-functor F₁ f))
        (λ d → naturality-natural-transformation-Precategory CD E F₁ F₂ α
          (f , id-hom-Precategory D))

    hom-curry-functor :
      hom-Precategory CDE2 (obj-curry-functor F₁) (obj-curry-functor F₂)
    pr1 hom-curry-functor = hom-hom-curry-functor
    pr2 hom-curry-functor = is-natural-hom-curry-functor

  map-curry-functor : map-Precategory CDE1 CDE2
  pr1 map-curry-functor = obj-curry-functor
  pr2 map-curry-functor {F₁} {F₂} = hom-curry-functor {F₁} {F₂}

  opaque
    preserves-comp-curry-functor :
      preserves-comp-hom-map-Precategory CDE1 CDE2 map-curry-functor
    preserves-comp-curry-functor {F₁} {F₂} {F₃} α₁ α₂ =
      eq-htpy-hom-family-natural-transformation-Precategory
      C DE
      (obj-curry-functor F₁) (obj-curry-functor F₃)
      (hom-curry-functor {F₁} {F₃}
        (comp-hom-Precategory CDE1 {F₁} {F₂} {F₃} α₁ α₂))
      (comp-hom-Precategory CDE2
        {obj-curry-functor F₁}
        {obj-curry-functor F₂}
        {obj-curry-functor F₃}
        (hom-curry-functor {F₂} {F₃} α₁)
        (hom-curry-functor {F₁} {F₂} α₂))
      (λ c → eq-htpy-hom-family-natural-transformation-Precategory
        D E
        (obj-obj-curry-functor F₁ c) (obj-obj-curry-functor F₃ c)
        (hom-hom-curry-functor {F₁} {F₃}
          (comp-hom-Precategory CDE1 {F₁} {F₂} {F₃} α₁ α₂) c)
        (comp-hom-Precategory DE
          {obj-obj-curry-functor F₁ c}
          {obj-obj-curry-functor F₂ c}
          {obj-obj-curry-functor F₃ c}
          (hom-hom-curry-functor {F₂} {F₃} α₁ c)
          (hom-hom-curry-functor {F₁} {F₂} α₂ c))
        (λ d → refl))

    preserves-id-curry-functor :
      preserves-id-hom-map-Precategory CDE1 CDE2 map-curry-functor
    preserves-id-curry-functor F =
      eq-htpy-hom-family-natural-transformation-Precategory
      C DE
      (obj-curry-functor F) (obj-curry-functor F)
      (hom-curry-functor {F} {F} (id-hom-Precategory CDE1 {F}))
      (id-hom-Precategory CDE2 {obj-curry-functor F})
      (λ c → eq-htpy-hom-family-natural-transformation-Precategory
        D E
        (obj-obj-curry-functor F c) (obj-obj-curry-functor F c)
        (hom-hom-curry-functor {F} {F} (id-hom-Precategory CDE1 {F}) c)
        (id-hom-Precategory DE {obj-obj-curry-functor F c})
        (λ d → refl))

  curry-functor : functor-Precategory CDE1 CDE2
  pr1 curry-functor = obj-curry-functor
  pr1 (pr2 curry-functor) {F₁} {F₂} = hom-curry-functor {F₁} {F₂}
  pr1 (pr2 (pr2 curry-functor)) {F₁} {F₂} {F₃} =
    preserves-comp-curry-functor {F₁} {F₂} {F₃}
  pr2 (pr2 (pr2 curry-functor)) = preserves-id-curry-functor
```
