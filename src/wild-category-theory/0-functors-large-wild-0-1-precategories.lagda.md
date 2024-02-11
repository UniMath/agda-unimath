# Functors between large wild (0,1)-precategories

```agda
module wild-category-theory.0-functors-large-wild-0-1-precategories where
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
open import foundation.wild-category-of-types

open import wild-category-theory.large-wild-0-1-precategories
open import wild-category-theory.maps-large-wild-0-1-precategories
```

</details>

## Idea

A
{{#concept "functor" Disambiguation="between large wild (0,1)-precategories" Agda=0-functor-Large-Wild-⟨0,1⟩-Precategory}}
between
[large wild (0,1)-precategories](wild-category-theory.large-wild-0-1-precategories.lagda.md)
is a map of objects `F₀ : Obj 𝒞 → Obj 𝒟` and a map of hom-types

```text
  F₁ x y : Hom 𝒞 x y → Hom 𝒟 (F₀ x) (F₀ y)
```

that preserves identities and composition.

## Definitions

### Functors between large wild (0,1)-precategories

```agda
record
  0-functor-Large-Wild-⟨0,1⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 γ1 γ2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒞 : Large-Wild-⟨0,1⟩-Precategory α1 β1 γ1)
  (𝒟 : Large-Wild-⟨0,1⟩-Precategory α2 β2 γ2)
  : UUω
  where

  constructor make-map-Large-Wild-⟨0,1⟩-Precategory

  field
    map-0-functor-Large-Wild-⟨0,1⟩-Precategory :
      map-Large-Wild-⟨0,1⟩-Precategory δ 𝒞 𝒟

  obj-0-functor-Large-Wild-⟨0,1⟩-Precategory :
    { l1 : Level} →
    obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1 →
    obj-Large-Wild-⟨0,1⟩-Precategory 𝒟 (δ l1)
  obj-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    obj-map-Large-Wild-⟨0,1⟩-Precategory
      ( map-0-functor-Large-Wild-⟨0,1⟩-Precategory)

  hom-0-functor-Large-Wild-⟨0,1⟩-Precategory :
    { l1 l2 : Level}
    { X : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1}
    { Y : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l2} →
    hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 X Y →
    hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
      ( obj-0-functor-Large-Wild-⟨0,1⟩-Precategory X)
      ( obj-0-functor-Large-Wild-⟨0,1⟩-Precategory Y)
  hom-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    hom-map-Large-Wild-⟨0,1⟩-Precategory
      ( map-0-functor-Large-Wild-⟨0,1⟩-Precategory)

  field
    preserves-comp-0-functor-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 l3 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1}
      {Y : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l2}
      {Z : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l3}
      ( g : hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 Y Z)
      ( f : hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 X Y) →
      relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
        ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory
          ( comp-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 g f))
        ( comp-hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
          ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory g)
          ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory f))

    preserves-id-0-functor-Large-Wild-⟨0,1⟩-Precategory :
      {l : Level} {X : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l} →
      relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
        ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory
          ( id-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 {X = X}))
        ( id-hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
          { X = obj-0-functor-Large-Wild-⟨0,1⟩-Precategory X})

    preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l1}
      {Y : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l2}
      {f g : hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 X Y} →
      relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 f g →
      relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒟
        ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory f)
        ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory g)

open 0-functor-Large-Wild-⟨0,1⟩-Precategory public
```

## Operations

### The identity functor on a large wild 0-precategory

```agda
module _
  {α : Level → Level} {β γ : Level → Level → Level}
  {𝒞 : Large-Wild-⟨0,1⟩-Precategory α β γ}
  where

  id-0-functor-Large-Wild-⟨0,1⟩-Precategory :
    0-functor-Large-Wild-⟨0,1⟩-Precategory (λ l → l) 𝒞 𝒞
  map-0-functor-Large-Wild-⟨0,1⟩-Precategory
    id-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    id-map-Large-Wild-⟨0,1⟩-Precategory
  preserves-comp-0-functor-Large-Wild-⟨0,1⟩-Precategory
    id-0-functor-Large-Wild-⟨0,1⟩-Precategory g f =
    refl-relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞
  preserves-id-0-functor-Large-Wild-⟨0,1⟩-Precategory
    id-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    refl-relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞
  preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory
    id-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    id
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
  (G : 0-functor-Large-Wild-⟨0,1⟩-Precategory δ1 ℬ 𝒞)
  (F : 0-functor-Large-Wild-⟨0,1⟩-Precategory δ2 𝒜 ℬ)
  where

  comp-0-functor-Large-Wild-⟨0,1⟩-Precategory :
    0-functor-Large-Wild-⟨0,1⟩-Precategory (λ l → δ1 (δ2 l)) 𝒜 𝒞
  comp-0-functor-Large-Wild-⟨0,1⟩-Precategory =
    λ where
      .map-0-functor-Large-Wild-⟨0,1⟩-Precategory →
        comp-map-Large-Wild-⟨0,1⟩-Precategory
          ( map-0-functor-Large-Wild-⟨0,1⟩-Precategory G)
          ( map-0-functor-Large-Wild-⟨0,1⟩-Precategory F)
      .preserves-comp-0-functor-Large-Wild-⟨0,1⟩-Precategory g f →
        comp-relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞
          ( preserves-comp-0-functor-Large-Wild-⟨0,1⟩-Precategory G
            ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory F g)
            ( hom-0-functor-Large-Wild-⟨0,1⟩-Precategory F f))
          ( preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory G
            ( preserves-comp-0-functor-Large-Wild-⟨0,1⟩-Precategory F g f))
      .preserves-id-0-functor-Large-Wild-⟨0,1⟩-Precategory →
        comp-relation-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞
          ( preserves-id-0-functor-Large-Wild-⟨0,1⟩-Precategory G)
          ( preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory G
            ( preserves-id-0-functor-Large-Wild-⟨0,1⟩-Precategory F))
      .preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory →
        ( preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory G ∘
          preserves-relation-hom-0-functor-Large-Wild-⟨0,1⟩-Precategory F)
```

### Postcomp

```agda
module _
  {α : Level → Level} {β γ : Level → Level → Level}
  {𝒞 : Large-Wild-⟨0,1⟩-Precategory α β γ}
  {l2 l3 : Level}
  {Y : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l2}
  {Z : obj-Large-Wild-⟨0,1⟩-Precategory 𝒞 l3}
  (f : hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 Y Z)
  where

  -- map-postcomp-Large-Wild-⟨0,1⟩-Precategory :
  --   map-Large-Wild-⟨0,1⟩-Precategory {!   !} 𝒞 {!   !}
  -- obj-map-Large-Wild-⟨0,1⟩-Precategory map-postcomp-Large-Wild-⟨0,1⟩-Precategory = {! hom-Large-Wild-⟨0,1⟩-Precategory 𝒞  !}
  -- hom-map-Large-Wild-⟨0,1⟩-Precategory map-postcomp-Large-Wild-⟨0,1⟩-Precategory x g = {! comp-hom-Large-Wild-⟨0,1⟩-Precategory 𝒞 g f !}
```
