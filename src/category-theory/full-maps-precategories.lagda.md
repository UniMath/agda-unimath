# Full maps between precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.full-maps-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.function-types funext
open import foundation.iterated-dependent-product-types funext
open import foundation.propositions funext univalence
open import foundation.surjective-maps funext univalence truncations
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **full** if
it's a [surjection](foundation.surjective-maps.md) on
hom-[sets](foundation-core.sets.md).

## Definition

### The predicate on maps between precategories of being full

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-full-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-full-map-Precategory =
    (x y : obj-Precategory C) →
    is-surjective (hom-map-Precategory C D F {x} {y})

  is-prop-is-full-map-Precategory : is-prop is-full-map-Precategory
  is-prop-is-full-map-Precategory =
    is-prop-iterated-Π 2
      ( λ x y → is-prop-is-surjective (hom-map-Precategory C D F {x} {y}))

  is-full-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-full-prop-map-Precategory = is-full-map-Precategory
  pr2 is-full-prop-map-Precategory = is-prop-is-full-map-Precategory
```

### The type of full maps between two precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  full-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  full-map-Precategory =
    Σ (map-Precategory C D) (is-full-map-Precategory C D)

  map-full-map-Precategory :
    full-map-Precategory → map-Precategory C D
  map-full-map-Precategory = pr1

  is-full-full-map-Precategory :
    (F : full-map-Precategory) →
    is-full-map-Precategory C D (map-full-map-Precategory F)
  is-full-full-map-Precategory = pr2

  obj-full-map-Precategory :
    full-map-Precategory → obj-Precategory C → obj-Precategory D
  obj-full-map-Precategory =
    obj-map-Precategory C D ∘ map-full-map-Precategory

  hom-full-map-Precategory :
    (F : full-map-Precategory) {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-full-map-Precategory F x)
      ( obj-full-map-Precategory F y)
  hom-full-map-Precategory =
    hom-map-Precategory C D ∘ map-full-map-Precategory
```
