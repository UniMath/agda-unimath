# Functors between large precategories

```agda
module category-theory.functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [large precategory](category-theory.large-precategories.md)
`C` to a large precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F id_x = id_(F x)`,
- `F (g ∘ f) = F g ∘ F f`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} (γ : Level → Level)
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  where

  record functor-Large-Precategory : UUω
    where
    constructor make-functor
    field
      obj-functor-Large-Precategory :
        { l1 : Level} →
        obj-Large-Precategory C l1 → obj-Large-Precategory D (γ l1)
      hom-functor-Large-Precategory :
        { l1 l2 : Level}
        { X : obj-Large-Precategory C l1}
        { Y : obj-Large-Precategory C l2} →
        hom-Large-Precategory C X Y →
        hom-Large-Precategory D
          ( obj-functor-Large-Precategory X)
          ( obj-functor-Large-Precategory Y)
      preserves-composition-functor-Large-Precategory :
        { l1 l2 l3 : Level}
        { X : obj-Large-Precategory C l1}
        { Y : obj-Large-Precategory C l2}
        { Z : obj-Large-Precategory C l3}
        ( g : hom-Large-Precategory C Y Z)
        ( f : hom-Large-Precategory C X Y) →
        ( hom-functor-Large-Precategory
          ( comp-hom-Large-Precategory C g f)) ＝
        ( comp-hom-Large-Precategory D
          ( hom-functor-Large-Precategory g)
          ( hom-functor-Large-Precategory f))
      preserves-identity-functor-Large-Precategory :
        { l1 : Level} {X : obj-Large-Precategory C l1} →
        ( hom-functor-Large-Precategory
          ( id-hom-Large-Precategory C {X = X})) ＝
        ( id-hom-Large-Precategory D {X = obj-functor-Large-Precategory X})

  open functor-Large-Precategory public
```

### The identity functor

There is an identity functor on any large precategory.

```agda
id-functor-Large-Precategory :
  {αC : Level → Level} {βC : Level → Level → Level} →
  {C : Large-Precategory αC βC} →
  functor-Large-Precategory id C C
obj-functor-Large-Precategory
  id-functor-Large-Precategory =
  id
hom-functor-Large-Precategory
  id-functor-Large-Precategory =
  id
preserves-composition-functor-Large-Precategory
  id-functor-Large-Precategory g f =
  refl
preserves-identity-functor-Large-Precategory
  id-functor-Large-Precategory =
  refl
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Large-Precategory :
  {αC αD αE γG γF : Level → Level}
  {βC βD βE : Level → Level → Level} →
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  {E : Large-Precategory αE βE} →
  functor-Large-Precategory γG D E →
  functor-Large-Precategory γF C D →
  functor-Large-Precategory (γG ∘ γF) C E
obj-functor-Large-Precategory
  ( comp-functor-Large-Precategory G F) =
  obj-functor-Large-Precategory G ∘ obj-functor-Large-Precategory F
hom-functor-Large-Precategory
  ( comp-functor-Large-Precategory G F) =
  hom-functor-Large-Precategory G ∘ hom-functor-Large-Precategory F
preserves-composition-functor-Large-Precategory
  ( comp-functor-Large-Precategory G F) g f =
  ( ap
    ( hom-functor-Large-Precategory G)
    ( preserves-composition-functor-Large-Precategory F g f)) ∙
  ( preserves-composition-functor-Large-Precategory G
    ( hom-functor-Large-Precategory F g)
    ( hom-functor-Large-Precategory F f))
preserves-identity-functor-Large-Precategory
  ( comp-functor-Large-Precategory G F) =
  ( ap
    ( hom-functor-Large-Precategory G)
    ( preserves-identity-functor-Large-Precategory F)) ∙
  ( preserves-identity-functor-Large-Precategory G)
```
