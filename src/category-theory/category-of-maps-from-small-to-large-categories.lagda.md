# The category of maps and natural transformations from small to large categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.category-of-maps-from-small-to-large-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.category-of-maps-categories funext univalence truncations
open import category-theory.isomorphisms-in-large-precategories funext univalence truncations
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.large-categories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations
open import category-theory.maps-from-small-to-large-categories funext univalence truncations
open import category-theory.maps-from-small-to-large-precategories funext univalence truncations
open import category-theory.natural-isomorphisms-maps-categories funext univalence truncations
open import category-theory.natural-isomorphisms-maps-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.precategory-of-maps-from-small-to-large-precategories funext univalence truncations

open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-from-small-to-large-categories.md) from small
[categories](category-theory.categories.md) to
[large categories](category-theory.large-categories.md) and
[natural transformations](category-theory.natural-transformations-maps-from-small-to-large-precategories.md)
between them form a large category whose identity map and composition structure
are inherited pointwise from the codomain category. This is called the
**category of maps from small to large categories**.

## Lemmas

### Extensionality of maps from small precategories to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (is-large-category-D : is-large-category-Large-Precategory D)
  where

  equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategory :
    {γ : Level}
    (F G : map-Small-Large-Precategory C D γ) →
    ( htpy-map-Small-Large-Precategory C D F G) ≃
    ( natural-isomorphism-map-Precategory C (precategory-Large-Precategory D γ)
      ( F)
      ( G))
  equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategory
    { γ} F G =
    equiv-natural-isomorphism-htpy-map-is-category-Precategory
      ( C)
      ( precategory-Large-Precategory D γ)
      ( is-category-is-large-category-Large-Precategory D is-large-category-D γ)
      ( F)
      ( G)

  extensionality-map-is-category-Small-Large-Precategory :
    {γ : Level}
    (F G : map-Small-Large-Precategory C D γ) →
    ( F ＝ G) ≃
    ( natural-isomorphism-map-Precategory C (precategory-Large-Precategory D γ)
      ( F)
      ( G))
  extensionality-map-is-category-Small-Large-Precategory F G =
    ( equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategory
      ( F)
      ( G)) ∘e
    ( equiv-htpy-eq-map-Small-Large-Precategory C D F G)
```

### When the codomain is a large category the map large precategory is a large category

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (is-large-category-D : is-large-category-Large-Precategory D)
  where

  abstract
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategory :
      is-large-category-Large-Precategory
        ( map-large-precategory-Small-Large-Precategory C D)
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategory
      { γ} F G =
      is-equiv-htpy'
        ( iso-eq-Precategory
          ( map-precategory-Small-Large-Precategory C D γ)
          ( F)
          ( G))
        ( compute-iso-eq-Large-Precategory
          ( map-large-precategory-Small-Large-Precategory C D)
          ( F)
          ( G))
        ( is-category-map-precategory-is-category-Precategory
          ( C)
          ( precategory-Large-Precategory D γ)
          ( is-category-is-large-category-Large-Precategory
            ( D)
            ( is-large-category-D)
            ( γ))
          ( F)
          ( G))
```

## Definitions

### The large category of maps and natural transformations from small to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  map-large-category-Small-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ α l ⊔ β l l) (λ l l' → l1 ⊔ l2 ⊔ β l l')
  large-precategory-Large-Category map-large-category-Small-Large-Category =
    map-large-precategory-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
  is-large-category-Large-Category map-large-category-Small-Large-Category =
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( is-large-category-Large-Category D)

  extensionality-map-Small-Large-Category :
    {γ : Level} (F G : map-Small-Large-Category C D γ) →
    (F ＝ G) ≃
    natural-isomorphism-map-Category C (category-Large-Category D γ) F G
  extensionality-map-Small-Large-Category {γ} =
    extensionality-map-Category C (category-Large-Category D γ)

  eq-natural-isomorphism-map-Small-Large-Category :
    {γ : Level} (F G : map-Small-Large-Category C D γ) →
    natural-isomorphism-map-Category C (category-Large-Category D γ) F G → F ＝ G
  eq-natural-isomorphism-map-Small-Large-Category F G =
    map-inv-equiv (extensionality-map-Small-Large-Category F G)
```

### The small categories of maps and natural transformations from small to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  map-category-Small-Large-Category :
    (l : Level) → Category (l1 ⊔ l2 ⊔ α l ⊔ β l l) (l1 ⊔ l2 ⊔ β l l)
  map-category-Small-Large-Category =
    category-Large-Category (map-large-category-Small-Large-Category C D)
```
