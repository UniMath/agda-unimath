# Maps between noncoherent large wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-large-wild-higher-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.large-globular-maps
open import structured-types.large-globular-types

open import wild-category-theory.maps-noncoherent-wild-higher-precategories
open import wild-category-theory.noncoherent-large-wild-higher-precategories
open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent large wild higher precategories" Agda=map-Noncoherent-Large-Wild-Higher-Precategory}}
`f` between
[noncoherent large wild higher precategories](wild-category-theory.noncoherent-large-wild-higher-precategories.md)
`𝒜` and `ℬ` is a [large globular map](structured-types.large-globular-maps.md)
between their underlying
[large globular types](structured-types.large-globular-types.md). More
specifically, maps between noncoherent large wild higher precategories consist
of a map on objects `F₀ : obj 𝒜 → obj ℬ`, and for every pair of $n$-morphisms
`f` and `g`, a map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent large wild higher precategories does not have to
preserve the identities or composition in any shape or form, and is the least
structured notion of a "morphism" between noncoherent wild higher precategories.
For a notion of "morphism" between noncoherent large wild higher precategories
that in one sense preserves this additional structure, see
[colax functors between noncoherent large wild higher precategories](wild-category-theory.colax-functors-noncoherent-large-wild-higher-precategories.md).

## Definitions

### Maps between noncoherent large wild higher precategories

```agda
map-Noncoherent-Large-Wild-Higher-Precategory :
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (δ : Level → Level)
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2) → UUω
map-Noncoherent-Large-Wild-Higher-Precategory δ 𝒜 ℬ =
  large-globular-map δ
    ( large-globular-type-Noncoherent-Large-Wild-Higher-Precategory 𝒜)
    ( large-globular-type-Noncoherent-Large-Wild-Higher-Precategory ℬ)

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2)
  (F : map-Noncoherent-Large-Wild-Higher-Precategory δ 𝒜 ℬ)
  where

  obj-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l →
    obj-Noncoherent-Large-Wild-Higher-Precategory ℬ (δ l)
  obj-map-Noncoherent-Large-Wild-Higher-Precategory =
    0-cell-large-globular-map F

  hom-globular-map-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    globular-map
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategory y))
  hom-globular-map-map-Noncoherent-Large-Wild-Higher-Precategory =
    1-cell-globular-map-large-globular-map F

  hom-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y →
    hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( obj-map-Noncoherent-Large-Wild-Higher-Precategory x)
      ( obj-map-Noncoherent-Large-Wild-Higher-Precategory y)
  hom-map-Noncoherent-Large-Wild-Higher-Precategory =
    1-cell-large-globular-map F

  2-hom-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategory f)
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategory g)
  2-hom-map-Noncoherent-Large-Wild-Higher-Precategory =
    2-cell-large-globular-map F

  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2) →
    map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( ℬ)
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategory y))
  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategory
    _ _ =
    1-cell-globular-map-large-globular-map F
```

### The identity map on a noncoherent large wild higher precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α β)
  where

  id-map-Noncoherent-Large-Wild-Higher-Precategory :
    map-Noncoherent-Large-Wild-Higher-Precategory (λ l → l) 𝒜 𝒜
  id-map-Noncoherent-Large-Wild-Higher-Precategory =
    id-large-globular-map _
```

### Composition of maps of noncoherent large wild higher precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2)
  (𝒞 : Noncoherent-Large-Wild-Higher-Precategory α3 β3)
  (G : map-Noncoherent-Large-Wild-Higher-Precategory δ2 ℬ 𝒞)
  (F : map-Noncoherent-Large-Wild-Higher-Precategory δ1 𝒜 ℬ)
  where

  comp-map-Noncoherent-Large-Wild-Higher-Precategory :
    map-Noncoherent-Large-Wild-Higher-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  comp-map-Noncoherent-Large-Wild-Higher-Precategory =
    comp-large-globular-map G F
```
