# Maps between noncoherent large wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-large-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.maps-globular-types
open import structured-types.maps-large-globular-types

open import wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent large wild $(∞,∞)$-precategories" Agda=map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory}}
`f` between
[noncoherent large wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` consists of a map on objects `F₀ : obj 𝒜 → obj ℬ`, and for every
pair of $n$-morphisms `f` and `g`, a map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

## Definitions

### Maps between noncoherent large wild $(∞,∞)$-precategories

```agda
record
  map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (δ : Level → Level)
  (𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2) : UUω
  where
  field
    obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l : Level} →
      obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l →
      obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ (δ l)

    hom-globular-type-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l1 l2 : Level}
      {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
      {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
      map-Globular-Type
        ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
        ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
          ( obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
          ( obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))

open map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2}
  (F : map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ 𝒜 ℬ)
  where

  hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x)
      ( obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F y)
  hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    0-cell-map-Globular-Type
      ( hom-globular-type-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F)

  2-hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    1-cell-map-Globular-Type
      ( hom-globular-type-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F)
```
