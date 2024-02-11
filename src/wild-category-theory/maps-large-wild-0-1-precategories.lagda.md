# Maps between large wild (0,1)-precategories

```agda
module wild-category-theory.maps-large-wild-0-1-precategories where
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

### Maps between large wild (0,1)-precategories

```agda
record
  map-Large-Wild-⟨0,1⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 γ1 γ2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒞 : Large-Wild-⟨0,1⟩-Precategory α1 β1 γ1)
  (𝒟 : Large-Wild-⟨0,1⟩-Precategory α2 β2 γ2)
  : UUω
  where

  constructor make-map-Large-Wild-⟨0,1⟩-Precategory

  field
    obj-map-Large-Wild-⟨0,1⟩-Precategory :
      { l1 : Level} →
      obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1 →
      obj-Large-Wild-⟨0,1⟩-Precategory 𝒟 (δ l1)

    hom-map-Large-Wild-⟨0,1⟩-Precategory :
      { l1 l2 : Level}
      { X : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1}
      { Y : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l2} →
      hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 X Y →
      hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
        ( obj-map-Large-Wild-⟨0,1⟩-Precategory X)
        ( obj-map-Large-Wild-⟨0,1⟩-Precategory Y)

open map-Large-Wild-⟨0,1⟩-Precategory public
```

## Operations

### The identity map on a large wild 0-precategory

```agda
module _
  {α : Level → Level} {β γ : Level → Level → Level}
  {𝒞 : Large-Wild-⟨0,1⟩-Precategory α β γ}
  where

  id-map-Large-Wild-⟨0,1⟩-Precategory :
    map-Large-Wild-⟨0,1⟩-Precategory (λ l → l) 𝒞 𝒞
  obj-map-Large-Wild-⟨0,1⟩-Precategory id-map-Large-Wild-⟨0,1⟩-Precategory = id
  hom-map-Large-Wild-⟨0,1⟩-Precategory id-map-Large-Wild-⟨0,1⟩-Precategory = id
```

### Composition of maps of large wild (0,1)-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 γ1 γ2 γ3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  {𝒜 : Large-Wild-⟨0,1⟩-Precategory α1 β1 γ1}
  {ℬ : Large-Wild-⟨0,1⟩-Precategory α2 β2 γ2}
  {𝒞 : Large-Wild-⟨0,1⟩-Precategory α3 β3 γ3}
  where

  comp-map-Large-Wild-⟨0,1⟩-Precategory :
    map-Large-Wild-⟨0,1⟩-Precategory δ1 ℬ 𝒞 →
    map-Large-Wild-⟨0,1⟩-Precategory δ2 𝒜 ℬ →
    map-Large-Wild-⟨0,1⟩-Precategory (λ l → δ1 (δ2 l)) 𝒜 𝒞
  obj-map-Large-Wild-⟨0,1⟩-Precategory
    ( comp-map-Large-Wild-⟨0,1⟩-Precategory G F) =
    obj-map-Large-Wild-⟨0,1⟩-Precategory G ∘
    obj-map-Large-Wild-⟨0,1⟩-Precategory F
  hom-map-Large-Wild-⟨0,1⟩-Precategory
    ( comp-map-Large-Wild-⟨0,1⟩-Precategory G F) =
    hom-map-Large-Wild-⟨0,1⟩-Precategory G ∘
    hom-map-Large-Wild-⟨0,1⟩-Precategory F
```
