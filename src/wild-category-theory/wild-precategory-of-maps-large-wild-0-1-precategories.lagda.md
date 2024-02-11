# The wild precategory of maps between large wild (0,1)-precategories

```agda
module wild-category-theory.wild-precategory-of-maps-large-wild-0-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import wild-category-theory.large-wild-0-1-precategories
open import wild-category-theory.maps-large-wild-0-1-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between large wild (0,1)-precategories" Agda=map-Large-Wild-⟨0,1⟩-Precategory}}
between
[large wild (0,1)-precategories](wild-category-theory.large-wild-0-1-precategories.md)
is a map of objects `F₀ : Obj 𝒞 → Obj 𝒟` and a map of hom-types

```text
  F₁ x y : Hom 𝒞 x y → Hom 𝒟 (F₀ x) (F₀ y).
```

**Note.** In contrast to
[0-functors](wild-category-theory.0-functorslarge-wild-0-1-precategories.md),
maps are _not_ asked to preserve identities, composition, or the
groupoid-relation on morphisms.

## Definitions

### The large wild (0,1)-precategory of maps between large wild (0,1)-precategories

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 γ1 γ2 : Level → Level → Level}
  {𝒞 : Large-Wild-⟨0,1⟩-Precategory α β γ}
  where

  map-large-wild-⟨0,1⟩-precategory-Large-Wild-⟨0,1⟩-Precategory :
```
