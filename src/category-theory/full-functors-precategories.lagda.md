# Full functors between precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.full-functors-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-maps-precategories funext univalence truncations
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.function-types funext
open import foundation.propositions funext univalence
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **full** if
it's [surjective](foundation.surjective-maps.md) on
hom-[sets](foundation-core.sets.md).

## Definition

### The predicate on functors between precategories of being full

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-full-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-full-functor-Precategory =
    is-full-map-Precategory C D (map-functor-Precategory C D F)

  is-prop-is-full-functor-Precategory :
    is-prop is-full-functor-Precategory
  is-prop-is-full-functor-Precategory =
    is-prop-is-full-map-Precategory C D (map-functor-Precategory C D F)

  is-full-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-full-prop-functor-Precategory =
    is-full-prop-map-Precategory C D (map-functor-Precategory C D F)
```

### The type of full functors between two precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  full-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  full-functor-Precategory =
    Σ (functor-Precategory C D) (is-full-functor-Precategory C D)

  functor-full-functor-Precategory :
    full-functor-Precategory → functor-Precategory C D
  functor-full-functor-Precategory = pr1

  is-full-full-functor-Precategory :
    (F : full-functor-Precategory) →
    is-full-functor-Precategory C D (functor-full-functor-Precategory F)
  is-full-full-functor-Precategory = pr2

  obj-full-functor-Precategory :
    full-functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-full-functor-Precategory =
    obj-functor-Precategory C D ∘ functor-full-functor-Precategory

  hom-full-functor-Precategory :
    (F : full-functor-Precategory) {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-full-functor-Precategory F x)
      ( obj-full-functor-Precategory F y)
  hom-full-functor-Precategory =
    hom-functor-Precategory C D ∘ functor-full-functor-Precategory
```
