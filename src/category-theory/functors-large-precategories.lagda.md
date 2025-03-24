# Functors between large precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.functors-large-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.function-types funext
open import foundation.identity-types funext
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
      preserves-comp-functor-Large-Precategory :
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
      preserves-id-functor-Large-Precategory :
        { l1 : Level} {X : obj-Large-Precategory C l1} →
        ( hom-functor-Large-Precategory
          ( id-hom-Large-Precategory C {X = X})) ＝
        ( id-hom-Large-Precategory D {X = obj-functor-Large-Precategory X})

  open functor-Large-Precategory public
```

### The identity functor

```agda
id-functor-Large-Precategory :
  {αC : Level → Level} {βC : Level → Level → Level} →
  (C : Large-Precategory αC βC) →
  functor-Large-Precategory (λ l → l) C C
obj-functor-Large-Precategory
  ( id-functor-Large-Precategory C) =
  id
hom-functor-Large-Precategory
  ( id-functor-Large-Precategory C) =
  id
preserves-comp-functor-Large-Precategory
  ( id-functor-Large-Precategory C) g f =
  refl
preserves-id-functor-Large-Precategory
  ( id-functor-Large-Precategory C) =
  refl
```

### Composition of functors

```agda
module _
  {αC αD αE γG γF : Level → Level}
  {βC βD βE : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (E : Large-Precategory αE βE)
  (G : functor-Large-Precategory γG D E)
  (F : functor-Large-Precategory γF C D)
  where

  obj-comp-functor-Large-Precategory :
    {l1 : Level} →
    obj-Large-Precategory C l1 → obj-Large-Precategory E (γG (γF l1))
  obj-comp-functor-Large-Precategory =
    obj-functor-Large-Precategory G ∘ obj-functor-Large-Precategory F

  hom-comp-functor-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2} →
    hom-Large-Precategory C X Y →
    hom-Large-Precategory E
      ( obj-comp-functor-Large-Precategory X)
      ( obj-comp-functor-Large-Precategory Y)
  hom-comp-functor-Large-Precategory =
    hom-functor-Large-Precategory G ∘ hom-functor-Large-Precategory F

  preserves-comp-comp-functor-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3}
    (g : hom-Large-Precategory C Y Z) (f : hom-Large-Precategory C X Y) →
    hom-comp-functor-Large-Precategory
      ( comp-hom-Large-Precategory C g f) ＝
    comp-hom-Large-Precategory E
      ( hom-comp-functor-Large-Precategory g)
      ( hom-comp-functor-Large-Precategory f)
  preserves-comp-comp-functor-Large-Precategory g f =
    ( ap
      ( hom-functor-Large-Precategory G)
      ( preserves-comp-functor-Large-Precategory F g f)) ∙
    ( preserves-comp-functor-Large-Precategory G
      ( hom-functor-Large-Precategory F g)
      ( hom-functor-Large-Precategory F f))

  preserves-id-comp-functor-Large-Precategory :
    {l1 : Level} {X : obj-Large-Precategory C l1} →
    hom-comp-functor-Large-Precategory (id-hom-Large-Precategory C {X = X}) ＝
    id-hom-Large-Precategory E
  preserves-id-comp-functor-Large-Precategory =
    ( ap
      ( hom-functor-Large-Precategory G)
      ( preserves-id-functor-Large-Precategory F)) ∙
    ( preserves-id-functor-Large-Precategory G)

  comp-functor-Large-Precategory :
    functor-Large-Precategory (λ l → γG (γF l)) C E
  obj-functor-Large-Precategory
    comp-functor-Large-Precategory =
    obj-comp-functor-Large-Precategory
  hom-functor-Large-Precategory
    comp-functor-Large-Precategory =
    hom-comp-functor-Large-Precategory
  preserves-comp-functor-Large-Precategory
    comp-functor-Large-Precategory =
    preserves-comp-comp-functor-Large-Precategory
  preserves-id-functor-Large-Precategory
    comp-functor-Large-Precategory =
    preserves-id-comp-functor-Large-Precategory
```
