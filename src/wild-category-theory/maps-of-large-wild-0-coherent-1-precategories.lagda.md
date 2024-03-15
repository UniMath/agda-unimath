# Maps between large wild 0-coherent 1-precategory

```agda
module wild-category-theory.maps-of-large-wild-0-coherent-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contratransitive-binary-relations
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.function-types
open import foundation.reflexive-relations
open import foundation.strict-symmetrization-binary-relations
open import foundation.transitive-binary-relations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.retractions

open import wild-category-theory.wild-1-pregroupoidal-relations
open import wild-category-theory.large-wild-0-coherent-1-precategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between large wild 0-coherent 1-precategories"}}
between large wild 0-coherent 1-precategories `F : 𝒞 → 𝒟` is a map on objects

```text
  F₀ : Ob 𝒞 → Ob 𝒟
```

and a map on morphisms

```text
  F₁ : hom 𝒞 x y → hom 𝒟 (F₀ x) (F₀ y)
```

for all objects `x`, `y` in `𝒞`.

## Definitions

### Maps between large wild 0-coherent 1-precategories

```agda
record
  map-Large-Wild-0-Coherent-1-Precategory
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level}
  (γ : Level → Level)
  (𝒞 : Large-Wild-0-Coherent-1-Precategory α1 β1)
  (𝒟 : Large-Wild-0-Coherent-1-Precategory α2 β2)
  : UUω
  where

  field
    obj-map-Large-Wild-0-Coherent-1-Precategory :
      {l : Level} →
      obj-Large-Wild-0-Coherent-1-Precategory 𝒞 l →
      obj-Large-Wild-0-Coherent-1-Precategory 𝒟 (γ l)

    hom-map-Large-Wild-0-Coherent-1-Precategory :
      {l1 l2 : Level}
      {x : obj-Large-Wild-0-Coherent-1-Precategory 𝒞 l1}
      {y : obj-Large-Wild-0-Coherent-1-Precategory 𝒞 l2} →
      hom-Large-Wild-0-Coherent-1-Precategory 𝒞 x y →
      hom-Large-Wild-0-Coherent-1-Precategory 𝒟
        ( obj-map-Large-Wild-0-Coherent-1-Precategory x)
        ( obj-map-Large-Wild-0-Coherent-1-Precategory y)

open map-Large-Wild-0-Coherent-1-Precategory public
```

### The identity map of large wild 0-coherent 1-precategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Large-Wild-0-Coherent-1-Precategory α β)
  where

  id-map-Large-Wild-0-Coherent-1-Precategory :
    map-Large-Wild-0-Coherent-1-Precategory (λ l → l) 𝒞 𝒞
  id-map-Large-Wild-0-Coherent-1-Precategory =
    λ where
    .obj-map-Large-Wild-0-Coherent-1-Precategory → id
    .hom-map-Large-Wild-0-Coherent-1-Precategory → id
```

### Composition of maps of large wild 0-coherent 1-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {γ1 γ2 : Level → Level}
  {𝒜 : Large-Wild-0-Coherent-1-Precategory α1 β1}
  {ℬ : Large-Wild-0-Coherent-1-Precategory α2 β2}
  {𝒞 : Large-Wild-0-Coherent-1-Precategory α3 β3}
  where

  comp-map-Large-Wild-0-Coherent-1-Precategory :
    map-Large-Wild-0-Coherent-1-Precategory γ2 ℬ 𝒞 →
    map-Large-Wild-0-Coherent-1-Precategory γ1 𝒜 ℬ →
    map-Large-Wild-0-Coherent-1-Precategory (λ l → γ2 (γ1 l)) 𝒜 𝒞
  comp-map-Large-Wild-0-Coherent-1-Precategory G F =
    λ where
      .obj-map-Large-Wild-0-Coherent-1-Precategory →
        G .obj-map-Large-Wild-0-Coherent-1-Precategory ∘
        F .obj-map-Large-Wild-0-Coherent-1-Precategory
      .hom-map-Large-Wild-0-Coherent-1-Precategory →
        G .hom-map-Large-Wild-0-Coherent-1-Precategory ∘
        F .hom-map-Large-Wild-0-Coherent-1-Precategory
```
