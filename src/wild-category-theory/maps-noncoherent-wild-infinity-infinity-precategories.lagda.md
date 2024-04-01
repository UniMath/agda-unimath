# Maps between noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.noncoherent-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent wild $(∞,∞)$-precategories" Agda=map-Noncoherent-Wild-⟨∞,∞⟩-Precategory}}
`f` between
[noncoherent wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` consists of a map on objects `F₀ : obj 𝒜 → obj ℬ`, and for every
pair of $n$-morphisms `f` and `g`, a map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent wild $(∞,∞)$-precategories does not have to preserve
the identities or composition in any shape or form, and is the least structured
notion of a "morphism" between noncoherent wild $(∞,∞)$-precategories. For a
notion of "morphism" between noncoherent wild $(∞,∞)$-precategories that in one
sense preserves this additional structure, see
[colax functors between noncoherent wild $(∞,∞)$-precategories](wild-category-theory.colax-functors-noncoherent-wild-infinity-infinity-precategories.md).

## Definitions

### Maps between noncoherent wild $(∞,∞)$-precategories

```agda
record
  map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  field
    obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 →
      obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ

    hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
      map-Globular-Type
        ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
        ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
          ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
          ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))

open map-Noncoherent-Wild-⟨∞,∞⟩-Precategory public

module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  (F : map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x)
      ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F y)
  hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    0-cell-map-Globular-Type
      ( hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)

  2-hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    1-cell-map-Globular-Type
      ( hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x)
        ( obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F y))
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    x y =
    λ where
    .obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    .hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      globular-type-1-cell-map-Globular-Type
        ( hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)
```

### The identity map on a noncoherent wild $(∞,∞)$-precategory

```agda
module _
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2)
  where

  id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒜
  id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      id
    .hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      id-map-Globular-Type _
```

### Composition of maps between noncoherent wild $(∞,∞)$-precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : map-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  comp-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒞
  comp-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory G ∘
      obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
    .hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory →
      comp-map-Globular-Type
        ( hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory G)
        ( hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)
```
