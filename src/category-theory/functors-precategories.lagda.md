# Functors between precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A functor from a precategory `C` to a precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F₁ id_x = id_(F₀ x)`,
- `F₁ (g ∘ f) = F₁ g ∘ F₁ f`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precategory =
    Σ ( obj-Precategory C → obj-Precategory D)
      ( λ F₀ →
        Σ ( {x y : obj-Precategory C} (f : type-hom-Precategory C x y) →
            type-hom-Precategory D (F₀ x) (F₀ y))
          ( λ F₁ →
            ( {x y z : obj-Precategory C} (g : type-hom-Precategory C y z)
              (f : type-hom-Precategory C x y) →
              ( F₁ (comp-hom-Precategory C g f)) ＝
              ( comp-hom-Precategory D (F₁ g) (F₁ f))) ×
            ( (x : obj-Precategory C) →
              F₁ (id-hom-Precategory C {x}) ＝ id-hom-Precategory D {F₀ x})))

  obj-functor-Precategory :
    functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-functor-Precategory = pr1

  hom-functor-Precategory :
    (F : functor-Precategory) →
    {x y : obj-Precategory C} →
    (f : type-hom-Precategory C x y) →
    type-hom-Precategory D
      ( obj-functor-Precategory F x)
      ( obj-functor-Precategory F y)
  hom-functor-Precategory F = pr1 (pr2 F)

  preserves-comp-functor-Precategory :
    (F : functor-Precategory) {x y z : obj-Precategory C}
    (g : type-hom-Precategory C y z) (f : type-hom-Precategory C x y) →
    ( hom-functor-Precategory F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( hom-functor-Precategory F g)
      ( hom-functor-Precategory F f))
  preserves-comp-functor-Precategory F = pr1 (pr2 (pr2 F))

  preserves-id-functor-Precategory :
    (F : functor-Precategory) (x : obj-Precategory C) →
    ( hom-functor-Precategory F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-functor-Precategory F x})
  preserves-id-functor-Precategory F = pr2 (pr2 (pr2 F))
```

## Examples

### The identity functor

There is an identity functor on any precategory.

```agda
id-functor-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → functor-Precategory C C
pr1 (id-functor-Precategory C) = id
pr1 (pr2 (id-functor-Precategory C)) = id
pr1 (pr2 (pr2 (id-functor-Precategory C))) g f = refl
pr2 (pr2 (pr2 (id-functor-Precategory C))) x = refl
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4) (E : Precategory l5 l6) →
  functor-Precategory D E → functor-Precategory C D → functor-Precategory C E
pr1 (comp-functor-Precategory C D E G F) =
  obj-functor-Precategory D E G ∘ obj-functor-Precategory C D F
pr1 (pr2 (comp-functor-Precategory C D E G F)) =
  hom-functor-Precategory D E G ∘ hom-functor-Precategory C D F
pr1 (pr2 (pr2 (comp-functor-Precategory C D E G F))) g f =
  ( ap
    ( hom-functor-Precategory D E G)
    ( preserves-comp-functor-Precategory C D F g f)) ∙
  ( preserves-comp-functor-Precategory D E G
    ( hom-functor-Precategory C D F g)
    ( hom-functor-Precategory C D F f))
pr2 (pr2 (pr2 (comp-functor-Precategory C D E G F))) x =
  ( ap
    ( hom-functor-Precategory D E G)
    ( preserves-id-functor-Precategory C D F x)) ∙
  ( preserves-id-functor-Precategory D E G (obj-functor-Precategory C D F x))
```

## Properties

### Respecting identities and compositions are propositions

This follows from the fact that the hom-types are sets.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-prop-preserves-comp-hom-Precategory :
    is-prop
      ( {x y z : obj-Precategory C}
        (g : type-hom-Precategory C y z) (f : type-hom-Precategory C x y) →
        ( hom-functor-Precategory C D F (comp-hom-Precategory C g f)) ＝
        ( comp-hom-Precategory D
          ( hom-functor-Precategory C D F g)
          ( hom-functor-Precategory C D F f)))
  is-prop-preserves-comp-hom-Precategory =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y →
            is-prop-Π'
              ( λ z →
                is-prop-Π
                  ( λ g →
                    is-prop-Π
                      ( λ f →
                        is-set-type-hom-Precategory D
                          ( obj-functor-Precategory C D F x)
                          ( obj-functor-Precategory C D F z)
                          ( hom-functor-Precategory C D F
                            ( comp-hom-Precategory C g f))
                          ( comp-hom-Precategory D
                            ( hom-functor-Precategory C D F g)
                            ( hom-functor-Precategory C D F f)))))))

  is-prop-preserves-id-hom-Precategory :
    is-prop
      ( (x : obj-Precategory C) →
        ( hom-functor-Precategory C D F (id-hom-Precategory C {x})) ＝
        ( id-hom-Precategory D {obj-functor-Precategory C D F x}))
  is-prop-preserves-id-hom-Precategory =
    is-prop-Π
      ( λ x →
        is-set-type-hom-Precategory D
          ( obj-functor-Precategory C D F x)
          ( obj-functor-Precategory C D F x)
          ( hom-functor-Precategory C D F (id-hom-Precategory C {x}))
          ( id-hom-Precategory D {obj-functor-Precategory C D F x}))
```
