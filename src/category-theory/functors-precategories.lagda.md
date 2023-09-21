# Functors on precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F₁ id_x = id_(F₀ x)`,
- `F₁ (g ∘ f) = F₁ g ∘ F₁ f`.

## Definition

### Maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Precategory =
    Σ ( obj-Precategory C → obj-Precategory D)
      ( λ F₀ →
        {x y : obj-Precategory C} →
        type-hom-Precategory C x y →
        type-hom-Precategory D (F₀ x) (F₀ y))

  map-obj-map-Precategory :
    (F : map-Precategory) → obj-Precategory C → obj-Precategory D
  map-obj-map-Precategory = pr1

  map-hom-map-Precategory :
    (F : map-Precategory)
    {x y : obj-Precategory C} →
    type-hom-Precategory C x y →
    type-hom-Precategory D
      ( map-obj-map-Precategory F x)
      ( map-obj-map-Precategory F y)
  map-hom-map-Precategory = pr2
```

### The predicate of being a functor on maps between Precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  preserves-comp-hom-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-map-Precategory =
    {x y z : obj-Precategory C}
    (g : type-hom-Precategory C y z) (f : type-hom-Precategory C x y) →
    ( map-hom-map-Precategory C D F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( map-hom-map-Precategory C D F g)
      ( map-hom-map-Precategory C D F f))

  preserves-id-hom-map-Precategory : UU (l1 ⊔ l4)
  preserves-id-hom-map-Precategory =
    (x : obj-Precategory C) →
    ( map-hom-map-Precategory C D F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {map-obj-map-Precategory C D F x})

  is-functor-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-functor-map-Precategory =
    preserves-comp-hom-map-Precategory ×
    preserves-id-hom-map-Precategory

  preserves-comp-hom-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-comp-hom-map-Precategory
  preserves-comp-hom-is-functor-map-Precategory = pr1

  preserves-id-hom-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-id-hom-map-Precategory
  preserves-id-hom-is-functor-map-Precategory = pr2
```

### Functors on Precategories

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
        Σ ( {x y : obj-Precategory C}
            (f : type-hom-Precategory C x y) →
            type-hom-Precategory D (F₀ x) (F₀ y))
          ( λ F₁ → is-functor-map-Precategory C D (F₀ , F₁)))

  map-obj-functor-Precategory :
    functor-Precategory → obj-Precategory C → obj-Precategory D
  map-obj-functor-Precategory = pr1

  map-hom-functor-Precategory :
    (F : functor-Precategory) →
    {x y : obj-Precategory C} →
    (f : type-hom-Precategory C x y) →
    type-hom-Precategory D
      ( map-obj-functor-Precategory F x)
      ( map-obj-functor-Precategory F y)
  map-hom-functor-Precategory F = pr1 (pr2 F)

  map-functor-Precategory : functor-Precategory → map-Precategory C D
  pr1 (map-functor-Precategory F) = map-obj-functor-Precategory F
  pr2 (map-functor-Precategory F) = map-hom-functor-Precategory F

  preserves-comp-functor-Precategory :
    (F : functor-Precategory) {x y z : obj-Precategory C}
    (g : type-hom-Precategory C y z) (f : type-hom-Precategory C x y) →
    ( map-hom-functor-Precategory F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( map-hom-functor-Precategory F g)
      ( map-hom-functor-Precategory F f))
  preserves-comp-functor-Precategory F = pr1 (pr2 (pr2 F))

  preserves-id-functor-Precategory :
    (F : functor-Precategory) (x : obj-Precategory C) →
    ( map-hom-functor-Precategory F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {map-obj-functor-Precategory F x})
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
  map-obj-functor-Precategory D E G ∘ map-obj-functor-Precategory C D F
pr1 (pr2 (comp-functor-Precategory C D E G F)) =
  map-hom-functor-Precategory D E G ∘ map-hom-functor-Precategory C D F
pr1 (pr2 (pr2 (comp-functor-Precategory C D E G F))) g f =
  ( ap
    ( map-hom-functor-Precategory D E G)
    ( preserves-comp-functor-Precategory C D F g f)) ∙
  ( preserves-comp-functor-Precategory D E G
    ( map-hom-functor-Precategory C D F g)
    ( map-hom-functor-Precategory C D F f))
pr2 (pr2 (pr2 (comp-functor-Precategory C D E G F))) x =
  ( ap
    ( map-hom-functor-Precategory D E G)
    ( preserves-id-functor-Precategory C D F x)) ∙
  ( preserves-id-functor-Precategory D E G
    ( map-obj-functor-Precategory C D F x))
```

## Properties

### Respecting identities and compositions are propositions

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-prop-preserves-comp-hom-map-Precategory :
    is-prop (preserves-comp-hom-map-Precategory C D F)
  is-prop-preserves-comp-hom-map-Precategory =
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
                          ( map-obj-map-Precategory C D F x)
                          ( map-obj-map-Precategory C D F z)
                          ( map-hom-map-Precategory C D F
                            ( comp-hom-Precategory C g f))
                          ( comp-hom-Precategory D
                            ( map-hom-map-Precategory C D F g)
                            ( map-hom-map-Precategory C D F f)))))))

  preserves-comp-hom-map-Precategory-Prop : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 preserves-comp-hom-map-Precategory-Prop =
    preserves-comp-hom-map-Precategory C D F
  pr2 preserves-comp-hom-map-Precategory-Prop =
    is-prop-preserves-comp-hom-map-Precategory

  is-prop-preserves-id-hom-map-Precategory :
    is-prop (preserves-id-hom-map-Precategory C D F)
  is-prop-preserves-id-hom-map-Precategory =
    is-prop-Π
      ( λ x →
        is-set-type-hom-Precategory D
          ( map-obj-map-Precategory C D F x)
          ( map-obj-map-Precategory C D F x)
          ( map-hom-map-Precategory C D F (id-hom-Precategory C {x}))
          ( id-hom-Precategory D {map-obj-map-Precategory C D F x}))

  preserves-id-hom-map-Precategory-Prop : Prop (l1 ⊔ l4)
  pr1 preserves-id-hom-map-Precategory-Prop =
    preserves-id-hom-map-Precategory C D F
  pr2 preserves-id-hom-map-Precategory-Prop =
    is-prop-preserves-id-hom-map-Precategory

  is-prop-is-functor-map-Precategory :
    is-prop (is-functor-map-Precategory C D F)
  is-prop-is-functor-map-Precategory =
    is-prop-prod
      ( is-prop-preserves-comp-hom-map-Precategory)
      ( is-prop-preserves-id-hom-map-Precategory)

  is-functor-map-Precategory-Prop : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-functor-map-Precategory-Prop = is-functor-map-Precategory C D F
  pr2 is-functor-map-Precategory-Prop = is-prop-is-functor-map-Precategory
```

### Extensionality of functors on precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  extensionality-functor-Precategory' :
    (F G : functor-Precategory C D) →
    (F ＝ G) ≃ (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  extensionality-functor-Precategory' F G =
    equiv-ap-emb
      ( comp-emb
        ( emb-subtype (is-functor-map-Precategory-Prop C D))
        ( emb-equiv
          ( inv-associative-Σ
            ( obj-Precategory C → obj-Precategory D)
            ( λ F₀ →
              { x y : obj-Precategory C} →
              type-hom-Precategory C x y →
              type-hom-Precategory D (F₀ x) (F₀ y))
            ( pr1 ∘ is-functor-map-Precategory-Prop C D))))
```

It remains to characterize equality of maps between precategories.
