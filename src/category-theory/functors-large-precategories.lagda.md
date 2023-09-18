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

- a map `F : C → D` on objects,
- a map `Fmap : hom x y → hom (F x) (F y)` on morphisms, such that the following
  identities hold:
- `Fmap id_x = id_(F x)`,
- `Fmap (g ∘ f) = F g ∘ F f`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  where

  record functor-Large-Precategory (γ : Level → Level) : UUω
    where
    constructor make-functor
    field
      map-obj-functor-Large-Precategory :
        { l1 : Level} →
        obj-Large-Precategory C l1 → obj-Large-Precategory D (γ l1)
      map-hom-functor-Large-Precategory :
        { l1 l2 : Level}
        { X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2} →
        type-hom-Large-Precategory C X Y →
        type-hom-Large-Precategory D
          ( map-obj-functor-Large-Precategory X)
          ( map-obj-functor-Large-Precategory Y)
      preserves-comp-functor-Large-Precategory :
        { l1 l2 l3 : Level}
        { X : obj-Large-Precategory C l1}
        { Y : obj-Large-Precategory C l2}
        { Z : obj-Large-Precategory C l3}
        ( g : type-hom-Large-Precategory C Y Z)
        ( f : type-hom-Large-Precategory C X Y) →
        ( map-hom-functor-Large-Precategory
          ( comp-hom-Large-Precategory C g f)) ＝
        ( comp-hom-Large-Precategory D
          ( map-hom-functor-Large-Precategory g)
          ( map-hom-functor-Large-Precategory f))
      preserves-id-functor-Large-Precategory :
        { l1 : Level} {X : obj-Large-Precategory C l1} →
        ( map-hom-functor-Large-Precategory
          ( id-hom-Large-Precategory C {X = X})) ＝
        ( id-hom-Large-Precategory D {X = map-obj-functor-Large-Precategory X})

  open functor-Large-Precategory public
```

## Examples

### The identity functor

There is an identity functor on any large precategory.

```agda
id-functor-Large-Precategory :
  {αC : Level → Level} {βC : Level → Level → Level} →
  {C : Large-Precategory αC βC} →
  functor-Large-Precategory C C (λ l → l)
map-obj-functor-Large-Precategory id-functor-Large-Precategory = id
map-hom-functor-Large-Precategory id-functor-Large-Precategory = id
preserves-comp-functor-Large-Precategory id-functor-Large-Precategory g f = refl
preserves-id-functor-Large-Precategory id-functor-Large-Precategory = refl
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
  functor-Large-Precategory D E γG → functor-Large-Precategory C D γF →
  functor-Large-Precategory C E (λ l → γG (γF l))
map-obj-functor-Large-Precategory (comp-functor-Large-Precategory G F) =
  map-obj-functor-Large-Precategory G ∘ map-obj-functor-Large-Precategory F
map-hom-functor-Large-Precategory (comp-functor-Large-Precategory G F) =
  map-hom-functor-Large-Precategory G ∘ map-hom-functor-Large-Precategory F
preserves-comp-functor-Large-Precategory
  ( comp-functor-Large-Precategory G F) g f =
  ( ap
    ( map-hom-functor-Large-Precategory G)
    ( preserves-comp-functor-Large-Precategory F g f)) ∙
  ( preserves-comp-functor-Large-Precategory G
    ( map-hom-functor-Large-Precategory F g)
    ( map-hom-functor-Large-Precategory F f))
preserves-id-functor-Large-Precategory (comp-functor-Large-Precategory G F) =
  ( ap
    ( map-hom-functor-Large-Precategory G)
    ( preserves-id-functor-Large-Precategory F)) ∙
  ( preserves-id-functor-Large-Precategory G)
```
