# Maps between noncoherent wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-wild-higher-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types

open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent wild higher precategories" Agda=map-Noncoherent-Wild-Higher-Precategory}}
`f` between
[noncoherent wild higher precategories](wild-category-theory.noncoherent-wild-higher-precategories.md)
`𝒜` and `ℬ` is a [globular map](structured-types.globular-maps.md) between their
underlying [globular types](structured-types.globular-types.md). More
specifically, a map `F` between noncoherent wild higher precategories consists
of a map on objects `F₀ : obj 𝒜 → obj ℬ`, and for every pair of $n$-morphisms
`f` and `g`, a map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent wild higher precategories does not have to preserve
the identities or composition in any shape or form, and is the least structured
notion of a "morphism" between noncoherent wild higher precategories. For a
notion of "morphism" between noncoherent wild higher precategories that in one
sense preserves this additional structure, see
[colax functors between noncoherent wild higher precategories](wild-category-theory.colax-functors-noncoherent-wild-higher-precategories.md).

## Definitions

### Maps between noncoherent wild higher precategories

```agda
map-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ =
  globular-map
    ( globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
    ( globular-type-Noncoherent-Wild-Higher-Precategory ℬ)

module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  obj-map-Noncoherent-Wild-Higher-Precategory :
    obj-Noncoherent-Wild-Higher-Precategory 𝒜 →
    obj-Noncoherent-Wild-Higher-Precategory ℬ
  obj-map-Noncoherent-Wild-Higher-Precategory =
    0-cell-globular-map F

  hom-globular-map-map-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    globular-map
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory ℬ
        ( obj-map-Noncoherent-Wild-Higher-Precategory x)
        ( obj-map-Noncoherent-Wild-Higher-Precategory y))
  hom-globular-map-map-Noncoherent-Wild-Higher-Precategory =
    1-cell-globular-map-globular-map F

  hom-map-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( obj-map-Noncoherent-Wild-Higher-Precategory x)
      ( obj-map-Noncoherent-Wild-Higher-Precategory y)
  hom-map-Noncoherent-Wild-Higher-Precategory =
    0-cell-globular-map
      ( hom-globular-map-map-Noncoherent-Wild-Higher-Precategory)

  2-hom-map-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( hom-map-Noncoherent-Wild-Higher-Precategory f)
      ( hom-map-Noncoherent-Wild-Higher-Precategory g)
  2-hom-map-Noncoherent-Wild-Higher-Precategory =
    1-cell-globular-map
      ( hom-globular-map-map-Noncoherent-Wild-Higher-Precategory)

  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
    map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( ℬ)
        ( obj-map-Noncoherent-Wild-Higher-Precategory x)
        ( obj-map-Noncoherent-Wild-Higher-Precategory y))
  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategory
    x y =
    1-cell-globular-map-globular-map F
```

### The identity map on a noncoherent wild higher precategory

```agda
module _
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  where

  id-map-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
  id-map-Noncoherent-Wild-Higher-Precategory =
    id-globular-map _
```

### Composition of maps between noncoherent wild higher precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6)
  (G : map-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  comp-map-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
  comp-map-Noncoherent-Wild-Higher-Precategory =
    comp-globular-map G F
```
