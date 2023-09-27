# Functors between precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
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

### The predicate of being a functor on maps between precategories

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
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-map-Precategory C D F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( hom-map-Precategory C D F g)
      ( hom-map-Precategory C D F f))

  preserves-id-hom-map-Precategory : UU (l1 ⊔ l4)
  preserves-id-hom-map-Precategory =
    (x : obj-Precategory C) →
    ( hom-map-Precategory C D F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-map-Precategory C D F x})

  is-functor-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-functor-map-Precategory =
    preserves-comp-hom-map-Precategory ×
    preserves-id-hom-map-Precategory

  preserves-comp-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-comp-hom-map-Precategory
  preserves-comp-is-functor-map-Precategory = pr1

  preserves-id-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-id-hom-map-Precategory
  preserves-id-is-functor-map-Precategory = pr2
```

### functors between precategories

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
            (f : hom-Precategory C x y) →
            hom-Precategory D (F₀ x) (F₀ y))
          ( λ F₁ → is-functor-map-Precategory C D (F₀ , F₁)))

  obj-functor-Precategory :
    functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-functor-Precategory = pr1

  hom-functor-Precategory :
    (F : functor-Precategory) →
    {x y : obj-Precategory C} →
    (f : hom-Precategory C x y) →
    hom-Precategory D
      ( obj-functor-Precategory F x)
      ( obj-functor-Precategory F y)
  hom-functor-Precategory F = pr1 (pr2 F)

  map-functor-Precategory : functor-Precategory → map-Precategory C D
  pr1 (map-functor-Precategory F) = obj-functor-Precategory F
  pr2 (map-functor-Precategory F) = hom-functor-Precategory F

  is-functor-functor-Precategory :
    (F : functor-Precategory) →
    is-functor-map-Precategory C D (map-functor-Precategory F)
  is-functor-functor-Precategory = pr2 ∘ pr2

  preserves-comp-functor-Precategory :
    (F : functor-Precategory) {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-functor-Precategory F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( hom-functor-Precategory F g)
      ( hom-functor-Precategory F f))
  preserves-comp-functor-Precategory F =
    preserves-comp-is-functor-map-Precategory C D
      ( map-functor-Precategory F)
      ( is-functor-functor-Precategory F)

  preserves-id-functor-Precategory :
    (F : functor-Precategory) (x : obj-Precategory C) →
    ( hom-functor-Precategory F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-functor-Precategory F x})
  preserves-id-functor-Precategory F =
    preserves-id-is-functor-map-Precategory C D
      ( map-functor-Precategory F)
      ( is-functor-functor-Precategory F)
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
  ( preserves-id-functor-Precategory D E G
    ( obj-functor-Precategory C D F x))
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
                is-prop-Π²
                  ( λ g f →
                    is-set-hom-Precategory D
                      ( obj-map-Precategory C D F x)
                      ( obj-map-Precategory C D F z)
                      ( hom-map-Precategory C D F
                        ( comp-hom-Precategory C g f))
                      ( comp-hom-Precategory D
                        ( hom-map-Precategory C D F g)
                        ( hom-map-Precategory C D F f))))))

  preserves-comp-hom-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 preserves-comp-hom-prop-map-Precategory =
    preserves-comp-hom-map-Precategory C D F
  pr2 preserves-comp-hom-prop-map-Precategory =
    is-prop-preserves-comp-hom-map-Precategory

  is-prop-preserves-id-hom-map-Precategory :
    is-prop (preserves-id-hom-map-Precategory C D F)
  is-prop-preserves-id-hom-map-Precategory =
    is-prop-Π
      ( λ x →
        is-set-hom-Precategory D
          ( obj-map-Precategory C D F x)
          ( obj-map-Precategory C D F x)
          ( hom-map-Precategory C D F (id-hom-Precategory C {x}))
          ( id-hom-Precategory D {obj-map-Precategory C D F x}))

  preserves-id-hom-prop-map-Precategory : Prop (l1 ⊔ l4)
  pr1 preserves-id-hom-prop-map-Precategory =
    preserves-id-hom-map-Precategory C D F
  pr2 preserves-id-hom-prop-map-Precategory =
    is-prop-preserves-id-hom-map-Precategory

  is-prop-is-functor-map-Precategory :
    is-prop (is-functor-map-Precategory C D F)
  is-prop-is-functor-map-Precategory =
    is-prop-prod
      ( is-prop-preserves-comp-hom-map-Precategory)
      ( is-prop-preserves-id-hom-map-Precategory)

  is-functor-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-functor-prop-map-Precategory = is-functor-map-Precategory C D F
  pr2 is-functor-prop-map-Precategory = is-prop-is-functor-map-Precategory
```

### Extensionality of functors between precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  equiv-eq-map-eq-functor-Precategory :
    (F ＝ G) ≃ (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  equiv-eq-map-eq-functor-Precategory =
    equiv-ap-emb
      ( comp-emb
        ( emb-subtype (is-functor-prop-map-Precategory C D))
        ( emb-equiv
          ( inv-associative-Σ
            ( obj-Precategory C → obj-Precategory D)
            ( λ F₀ →
              { x y : obj-Precategory C} →
              hom-Precategory C x y →
              hom-Precategory D (F₀ x) (F₀ y))
            ( pr1 ∘ is-functor-prop-map-Precategory C D))))

  eq-map-eq-functor-Precategory :
    (F ＝ G) → (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  eq-map-eq-functor-Precategory =
    map-equiv equiv-eq-map-eq-functor-Precategory

  eq-eq-map-functor-Precategory :
    (map-functor-Precategory C D F ＝ map-functor-Precategory C D G) → (F ＝ G)
  eq-eq-map-functor-Precategory =
    map-inv-equiv equiv-eq-map-eq-functor-Precategory

  is-section-eq-eq-map-functor-Precategory :
    eq-map-eq-functor-Precategory ∘ eq-eq-map-functor-Precategory ~ id
  is-section-eq-eq-map-functor-Precategory =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Precategory

  is-retraction-eq-eq-map-functor-Precategory :
    eq-eq-map-functor-Precategory ∘ eq-map-eq-functor-Precategory ~ id
  is-retraction-eq-eq-map-functor-Precategory =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Precategory
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  htpy-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-functor-Precategory =
    htpy-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  equiv-htpy-eq-functor-Precategory : (F ＝ G) ≃ htpy-functor-Precategory
  equiv-htpy-eq-functor-Precategory =
    ( equiv-htpy-eq-map-Precategory C D)
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G) ∘e
    ( equiv-eq-map-eq-functor-Precategory C D F G)

  htpy-eq-functor-Precategory : F ＝ G → htpy-functor-Precategory
  htpy-eq-functor-Precategory =
    map-equiv equiv-htpy-eq-functor-Precategory

  eq-htpy-functor-Precategory : htpy-functor-Precategory → F ＝ G
  eq-htpy-functor-Precategory =
    map-inv-equiv equiv-htpy-eq-functor-Precategory

  is-section-eq-htpy-functor-Precategory :
    htpy-eq-functor-Precategory ∘ eq-htpy-functor-Precategory ~ id
  is-section-eq-htpy-functor-Precategory =
    is-section-map-inv-equiv equiv-htpy-eq-functor-Precategory

  is-retraction-eq-htpy-functor-Precategory :
    eq-htpy-functor-Precategory ∘ htpy-eq-functor-Precategory ~ id
  is-retraction-eq-htpy-functor-Precategory =
    is-retraction-map-inv-equiv equiv-htpy-eq-functor-Precategory
```

### Functors preserve isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  {x y : obj-Precategory C}
  where

  preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    is-iso-Precategory C f →
    is-iso-Precategory D (hom-functor-Precategory C D F f)
  pr1 (preserves-is-iso-functor-Precategory f is-iso-f) =
    hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f)
  pr1 (pr2 (preserves-is-iso-functor-Precategory f is-iso-f)) =
    ( inv
      ( preserves-comp-functor-Precategory C D F
        ( f)
        ( hom-inv-is-iso-Precategory C is-iso-f))) ∙
    ( ap
      ( hom-functor-Precategory C D F)
      ( is-section-hom-inv-is-iso-Precategory C is-iso-f)) ∙
    ( preserves-id-functor-Precategory C D F y)
  pr2 (pr2 (preserves-is-iso-functor-Precategory f is-iso-f)) =
    ( inv
      ( preserves-comp-functor-Precategory C D F
        ( hom-inv-is-iso-Precategory C is-iso-f)
        ( f))) ∙
    ( ap
      ( hom-functor-Precategory C D F)
      ( is-retraction-hom-inv-is-iso-Precategory C is-iso-f)) ∙
    ( preserves-id-functor-Precategory C D F x)

  preserves-iso-functor-Precategory :
    iso-Precategory C x y →
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y)
  pr1 (preserves-iso-functor-Precategory f) =
    hom-functor-Precategory C D F (hom-iso-Precategory C f)
  pr2 (preserves-iso-functor-Precategory f) =
    preserves-is-iso-functor-Precategory
      ( hom-iso-Precategory C f)
      ( is-iso-iso-Precategory C f)
```

## See also

- [The precategory of functors and natural transformations between precategories](category-theory.precategory-of-functors.md)
