# Anafunctors between precategories

```agda
module category-theory.anafunctors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

An **anafunctor** is a [functor](category-theory.functors-precategories.md) that
is only defined up to
[isomorphism](category-theory.isomorphisms-in-precategories.md).

## Definition

```agda
anafunctor-Precategory :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Precategory l1 l2 → Precategory l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Precategory l C D =
  Σ ( obj-Precategory C → obj-Precategory D → UU l)
    ( λ F₀ →
      Σ ( ( X Y : obj-Precategory C)
          ( U : obj-Precategory D) (u : F₀ X U) →
          ( V : obj-Precategory D) (v : F₀ Y V) →
          ( f : type-hom-Precategory C X Y) → type-hom-Precategory D U V)
        ( λ F₁ →
          ( ( X : obj-Precategory C) →
            type-trunc-Prop (Σ (obj-Precategory D) (F₀ X))) ×
          ( ( ( X : obj-Precategory C)
              ( U : obj-Precategory D) (u : F₀ X U) →
              F₁ X X U u U u (id-hom-Precategory C) ＝ id-hom-Precategory D) ×
            ( ( X Y Z : obj-Precategory C)
              ( U : obj-Precategory D) (u : F₀ X U)
              ( V : obj-Precategory D) (v : F₀ Y V)
              ( W : obj-Precategory D) (w : F₀ Z W) →
              ( g : type-hom-Precategory C Y Z)
              ( f : type-hom-Precategory C X Y) →
              ( F₁ X Z U u W w (comp-hom-Precategory C g f)) ＝
              ( comp-hom-Precategory D
                ( F₁ Y Z V v W w g)
                ( F₁ X Y U u V v f))))))

module _
  {l1 l2 l3 l4 l5 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : anafunctor-Precategory l5 C D)
  where

  object-anafunctor-Precategory : obj-Precategory C → obj-Precategory D → UU l5
  object-anafunctor-Precategory = pr1 F

  hom-anafunctor-Precategory :
    (X Y : obj-Precategory C)
    (U : obj-Precategory D) (u : object-anafunctor-Precategory X U)
    (V : obj-Precategory D) (v : object-anafunctor-Precategory Y V) →
    type-hom-Precategory C X Y → type-hom-Precategory D U V
  hom-anafunctor-Precategory = pr1 (pr2 F)
```

## Properties

### Any functor between precategories induces an anafunctor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  anafunctor-functor-Precategory :
    functor-Precategory C D → anafunctor-Precategory l4 C D
  pr1 (anafunctor-functor-Precategory F) X Y =
    iso-Precategory D (obj-functor-Precategory C D F X) Y
  pr1 (pr2 (anafunctor-functor-Precategory F)) X Y U u V v f =
    comp-hom-Precategory D
      ( comp-hom-Precategory D
        ( hom-iso-Precategory D v)
        ( hom-functor-Precategory C D F f))
      ( hom-inv-iso-Precategory D u)
  pr1 (pr2 (pr2 (anafunctor-functor-Precategory F))) X =
    unit-trunc-Prop
      ( pair (obj-functor-Precategory C D F X) (id-iso-Precategory D))
  pr1 (pr2 (pr2 (pr2 (anafunctor-functor-Precategory F)))) X U u =
    ( ap
      ( comp-hom-Precategory' D (hom-inv-iso-Precategory D u))
      ( ( ap
          ( comp-hom-Precategory D (hom-iso-Precategory D u))
          ( preserves-id-functor-Precategory C D F X)) ∙
        ( right-unit-law-comp-hom-Precategory D (hom-iso-Precategory D u)))) ∙
    ( is-section-hom-inv-iso-Precategory D u)
  pr2 (pr2 (pr2 (pr2 (anafunctor-functor-Precategory F))))
    X Y Z U u V v W w g f =
    ( ap
      ( comp-hom-Precategory' D (hom-inv-iso-Precategory D u))
      ( ( ( ap
            ( comp-hom-Precategory D (hom-iso-Precategory D w))
            ( preserves-comp-functor-Precategory C D F g f)) ∙
          ( ( inv
              ( associative-comp-hom-Precategory D
                ( hom-iso-Precategory D w)
                ( hom-functor-Precategory C D F g)
                ( hom-functor-Precategory C D F f))) ∙
            ( ap
              ( comp-hom-Precategory' D (hom-functor-Precategory C D F f))
              ( ( inv
                  ( right-unit-law-comp-hom-Precategory D
                    ( comp-hom-Precategory D
                      ( hom-iso-Precategory D w)
                      ( hom-functor-Precategory C D F g)))) ∙
                ( ( ap
                    ( comp-hom-Precategory D
                      ( comp-hom-Precategory D
                        ( hom-iso-Precategory D w)
                        ( hom-functor-Precategory C D F g)))
                      ( inv (is-retraction-hom-inv-iso-Precategory D v))) ∙
                  ( inv
                    ( associative-comp-hom-Precategory D
                      ( comp-hom-Precategory D
                        ( hom-iso-Precategory D w)
                        ( hom-functor-Precategory C D F g))
                      ( hom-inv-iso-Precategory D v)
                      ( hom-iso-Precategory D v)))))))) ∙
        ( associative-comp-hom-Precategory D
          ( comp-hom-Precategory D
            ( comp-hom-Precategory D
              ( hom-iso-Precategory D w)
              ( hom-functor-Precategory C D F g))
            ( hom-inv-iso-Precategory D v))
          ( hom-iso-Precategory D v)
          ( hom-functor-Precategory C D F f)))) ∙
    ( associative-comp-hom-Precategory D
      ( comp-hom-Precategory D
        ( comp-hom-Precategory D
          ( hom-iso-Precategory D w)
          ( hom-functor-Precategory C D F g))
        ( hom-inv-iso-Precategory D v))
      ( comp-hom-Precategory D
        ( hom-iso-Precategory D v)
        ( hom-functor-Precategory C D F f))
      ( hom-inv-iso-Precategory D u))
```
