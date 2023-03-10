# Functors between precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A functor from a precategory `C` to a precategory `D` consists of:
- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms,
such that the following identities hold:
- `F₁ id_x = id_(F₀ x)`,
- `F₁ (comp g f) = comp (F₁ g) (F₁ f)`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  where

  functor-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precat =
    Σ ( obj-Precat C → obj-Precat D)
      ( λ F₀ →
        Σ ( {x y : obj-Precat C} (f : type-hom-Precat C x y) →
            type-hom-Precat D (F₀ x) (F₀ y))
          ( λ F₁ →
            ( {x y z : obj-Precat C} (g : type-hom-Precat C y z)
              (f : type-hom-Precat C x y) →
              F₁ (comp-hom-Precat C g f) ＝ comp-hom-Precat D (F₁ g) (F₁ f)) ×
            ( (x : obj-Precat C) →
              F₁ (id-hom-Precat C {x}) ＝ id-hom-Precat D {F₀ x})))

  obj-functor-Precat : functor-Precat → obj-Precat C → obj-Precat D
  obj-functor-Precat = pr1

  hom-functor-Precat :
    (F : functor-Precat) →
    {x y : obj-Precat C} →
    (f : type-hom-Precat C x y) →
    type-hom-Precat D (obj-functor-Precat F x) (obj-functor-Precat F y)
  hom-functor-Precat F = pr1 (pr2 F)

  respects-comp-functor-Precat :
    (F : functor-Precat) {x y z : obj-Precat C}
    (g : type-hom-Precat C y z) (f : type-hom-Precat C x y) →
    ( hom-functor-Precat F (comp-hom-Precat C g f)) ＝
    ( comp-hom-Precat D (hom-functor-Precat F g) (hom-functor-Precat F f))
  respects-comp-functor-Precat F = pr1 (pr2 (pr2 F))

  respects-id-functor-Precat :
    (F : functor-Precat) (x : obj-Precat C) →
    ( hom-functor-Precat F (id-hom-Precat C {x})) ＝
    ( id-hom-Precat D {obj-functor-Precat F x})
  respects-id-functor-Precat F = pr2 (pr2 (pr2 F))
```

## Examples

### The identity functor

There is an identity functor on any precategory.

```agda
id-functor-Precat : ∀ {l1 l2} (C : Precat l1 l2) → functor-Precat C C
pr1 (id-functor-Precat C) = id
pr1 (pr2 (id-functor-Precat C)) = id
pr1 (pr2 (pr2 (id-functor-Precat C))) g f = refl
pr2 (pr2 (pr2 (id-functor-Precat C))) x = refl
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Precat :
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precat l1 l2) (D : Precat l3 l4) (E : Precat l5 l6) →
  functor-Precat D E → functor-Precat C D → functor-Precat C E
pr1 (comp-functor-Precat C D E G F) =
  obj-functor-Precat D E G ∘ obj-functor-Precat C D F
pr1 (pr2 (comp-functor-Precat C D E G F)) =
  hom-functor-Precat D E G ∘ hom-functor-Precat C D F
pr1 (pr2 (pr2 (comp-functor-Precat C D E G F))) g f =
  ( ap (hom-functor-Precat D E G) (respects-comp-functor-Precat C D F g f)) ∙
  ( respects-comp-functor-Precat D E G
    ( hom-functor-Precat C D F g)
    ( hom-functor-Precat C D F f))
pr2 (pr2 (pr2 (comp-functor-Precat C D E G F))) x =
  ( ap (hom-functor-Precat D E G) (respects-id-functor-Precat C D F x)) ∙
  ( respects-id-functor-Precat D E G (obj-functor-Precat C D F x))
```

## Properties

### Respecting identities and compositions are propositions

This follows from the fact that the hom-types are sets.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F : functor-Precat C D)
  where

  is-prop-respects-comp-hom-Precat :
    is-prop
      ( {x y z : obj-Precat C}
        (g : type-hom-Precat C y z) (f : type-hom-Precat C x y) →
        ( hom-functor-Precat C D F (comp-hom-Precat C g f)) ＝
        ( comp-hom-Precat D
          ( hom-functor-Precat C D F g)
          ( hom-functor-Precat C D F f)))
  is-prop-respects-comp-hom-Precat =
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
                        is-set-type-hom-Precat D
                          ( obj-functor-Precat C D F x)
                          ( obj-functor-Precat C D F z)
                          ( hom-functor-Precat C D F (comp-hom-Precat C g f))
                          ( comp-hom-Precat D
                            ( hom-functor-Precat C D F g)
                            ( hom-functor-Precat C D F f)))))))

  is-prop-respects-id-hom-Precat :
    is-prop
      ( (x : obj-Precat C) →
        ( hom-functor-Precat C D F (id-hom-Precat C {x})) ＝
        ( id-hom-Precat D {obj-functor-Precat C D F x}))
  is-prop-respects-id-hom-Precat =
    is-prop-Π
      ( λ x →
        is-set-type-hom-Precat D
          ( obj-functor-Precat C D F x)
          ( obj-functor-Precat C D F x)
          ( hom-functor-Precat C D F (id-hom-Precat C {x}))
          ( id-hom-Precat D {obj-functor-Precat C D F x}))
```
