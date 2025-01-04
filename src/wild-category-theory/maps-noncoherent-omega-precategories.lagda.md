# Maps between noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types

open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent ω-precategories" Agda=map-Noncoherent-ω-Precategory}}
`f` between
[noncoherent ω-precategories](wild-category-theory.noncoherent-omega-precategories.md)
`𝒜` and `ℬ` is a [globular map](globular-types.globular-maps.md) between their
underlying [globular types](globular-types.globular-types.md). More
specifically, a map `F` between noncoherent ω-precategories consists of a map on
objects `F₀ : obj 𝒜 → obj ℬ`, and for every pair of $n$-morphisms `f` and `g`, a
map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent ω-precategories does not have to preserve the
identities or composition in any shape or form, and is the least structured
notion of a "morphism" between noncoherent ω-precategories. For a notion of
"morphism" between noncoherent ω-precategories that in one sense preserves this
additional structure, see
[colax functors between noncoherent ω-precategories](wild-category-theory.colax-functors-noncoherent-omega-precategories.md).

## Definitions

### Maps between noncoherent ω-precategories

```agda
map-Noncoherent-ω-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
map-Noncoherent-ω-Precategory 𝒜 ℬ =
  globular-map
    ( globular-type-Noncoherent-ω-Precategory 𝒜)
    ( globular-type-Noncoherent-ω-Precategory ℬ)

module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (F : map-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  obj-map-Noncoherent-ω-Precategory :
    obj-Noncoherent-ω-Precategory 𝒜 →
    obj-Noncoherent-ω-Precategory ℬ
  obj-map-Noncoherent-ω-Precategory =
    0-cell-globular-map F

  hom-globular-map-map-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    globular-map
      ( hom-globular-type-Noncoherent-ω-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-ω-Precategory ℬ
        ( obj-map-Noncoherent-ω-Precategory x)
        ( obj-map-Noncoherent-ω-Precategory y))
  hom-globular-map-map-Noncoherent-ω-Precategory =
    1-cell-globular-map-globular-map F

  hom-map-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    hom-Noncoherent-ω-Precategory 𝒜 x y →
    hom-Noncoherent-ω-Precategory ℬ
      ( obj-map-Noncoherent-ω-Precategory x)
      ( obj-map-Noncoherent-ω-Precategory y)
  hom-map-Noncoherent-ω-Precategory =
    0-cell-globular-map
      ( hom-globular-map-map-Noncoherent-ω-Precategory)

  2-hom-map-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜}
    {f g : hom-Noncoherent-ω-Precategory 𝒜 x y} →
    2-hom-Noncoherent-ω-Precategory 𝒜 f g →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( hom-map-Noncoherent-ω-Precategory f)
      ( hom-map-Noncoherent-ω-Precategory g)
  2-hom-map-Noncoherent-ω-Precategory =
    1-cell-globular-map
      ( hom-globular-map-map-Noncoherent-ω-Precategory)

  hom-noncoherent-ω-precategory-map-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory 𝒜) →
    map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( ℬ)
        ( obj-map-Noncoherent-ω-Precategory x)
        ( obj-map-Noncoherent-ω-Precategory y))
  hom-noncoherent-ω-precategory-map-Noncoherent-ω-Precategory
    x y =
    1-cell-globular-map-globular-map F
```

### The identity map on a noncoherent ω-precategory

```agda
module _
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2)
  where

  id-map-Noncoherent-ω-Precategory :
    map-Noncoherent-ω-Precategory 𝒜 𝒜
  id-map-Noncoherent-ω-Precategory =
    id-globular-map _
```

### Composition of maps between noncoherent ω-precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (𝒞 : Noncoherent-ω-Precategory l5 l6)
  (G : map-Noncoherent-ω-Precategory ℬ 𝒞)
  (F : map-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  comp-map-Noncoherent-ω-Precategory :
    map-Noncoherent-ω-Precategory 𝒜 𝒞
  comp-map-Noncoherent-ω-Precategory =
    comp-globular-map G F
```
