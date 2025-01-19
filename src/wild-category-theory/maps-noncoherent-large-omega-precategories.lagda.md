# Maps between noncoherent large ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-large-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.large-globular-maps
open import globular-types.large-globular-types

open import wild-category-theory.maps-noncoherent-omega-precategories
open import wild-category-theory.noncoherent-large-omega-precategories
open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent large ω-precategories" Agda=map-Noncoherent-Large-ω-Precategory}}
`f` between
[noncoherent large ω-precategories](wild-category-theory.noncoherent-large-omega-precategories.md)
`𝒜` and `ℬ` is a [large globular map](globular-types.large-globular-maps.md)
between their underlying
[large globular types](globular-types.large-globular-types.md). More
specifically, maps between noncoherent large ω-precategories consist of a map on
objects `F₀ : obj 𝒜 → obj ℬ`, and for every pair of $n$-morphisms `f` and `g`, a
map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent large ω-precategories does not have to preserve the
identities or composition in any shape or form, and is the least structured
notion of a "morphism" between noncoherent ω-precategories. For a notion of
"morphism" between noncoherent large ω-precategories that in one sense preserves
this additional structure, see
[colax functors between noncoherent large ω-precategories](wild-category-theory.colax-functors-noncoherent-large-omega-precategories.md).

## Definitions

### Maps between noncoherent large ω-precategories

```agda
map-Noncoherent-Large-ω-Precategory :
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (δ : Level → Level)
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2) → UUω
map-Noncoherent-Large-ω-Precategory δ 𝒜 ℬ =
  large-globular-map δ
    ( large-globular-type-Noncoherent-Large-ω-Precategory 𝒜)
    ( large-globular-type-Noncoherent-Large-ω-Precategory ℬ)

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2)
  (F : map-Noncoherent-Large-ω-Precategory δ 𝒜 ℬ)
  where

  obj-map-Noncoherent-Large-ω-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-ω-Precategory 𝒜 l →
    obj-Noncoherent-Large-ω-Precategory ℬ (δ l)
  obj-map-Noncoherent-Large-ω-Precategory =
    0-cell-large-globular-map F

  hom-globular-map-map-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    globular-map
      ( hom-globular-type-Noncoherent-Large-ω-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-ω-Precategory ℬ
        ( obj-map-Noncoherent-Large-ω-Precategory x)
        ( obj-map-Noncoherent-Large-ω-Precategory y))
  hom-globular-map-map-Noncoherent-Large-ω-Precategory =
    1-cell-globular-map-large-globular-map F

  hom-map-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-ω-Precategory 𝒜 x y →
    hom-Noncoherent-Large-ω-Precategory ℬ
      ( obj-map-Noncoherent-Large-ω-Precategory x)
      ( obj-map-Noncoherent-Large-ω-Precategory y)
  hom-map-Noncoherent-Large-ω-Precategory =
    1-cell-large-globular-map F

  2-hom-map-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-ω-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-ω-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-map-Noncoherent-Large-ω-Precategory f)
      ( hom-map-Noncoherent-Large-ω-Precategory g)
  2-hom-map-Noncoherent-Large-ω-Precategory =
    2-cell-large-globular-map F

  hom-noncoherent-ω-precategory-map-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2) →
    map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( ℬ)
        ( obj-map-Noncoherent-Large-ω-Precategory x)
        ( obj-map-Noncoherent-Large-ω-Precategory y))
  hom-noncoherent-ω-precategory-map-Noncoherent-Large-ω-Precategory
    _ _ =
    1-cell-globular-map-large-globular-map F
```

### The identity map on a noncoherent large ω-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α β)
  where

  id-map-Noncoherent-Large-ω-Precategory :
    map-Noncoherent-Large-ω-Precategory (λ l → l) 𝒜 𝒜
  id-map-Noncoherent-Large-ω-Precategory =
    id-large-globular-map _
```

### Composition of maps of noncoherent large ω-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2)
  (𝒞 : Noncoherent-Large-ω-Precategory α3 β3)
  (G : map-Noncoherent-Large-ω-Precategory δ2 ℬ 𝒞)
  (F : map-Noncoherent-Large-ω-Precategory δ1 𝒜 ℬ)
  where

  comp-map-Noncoherent-Large-ω-Precategory :
    map-Noncoherent-Large-ω-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  comp-map-Noncoherent-Large-ω-Precategory =
    comp-large-globular-map G F
```
