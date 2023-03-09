# Natural transformations between functors between large precategories

```agda
module category-theory.natural-transformations-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given large precategories `C` and `D`, a natural transformation from a functor `F : C → D` to `G : C → D` consists of :
- a family of morphisms `γ : (x : C) → hom (F x) (G x)`
such that the following identity holds:
- `comp (G f) (γ x) = comp (γ y) (F f)`, for all `f : hom x y`.

## Definition

```agda
square-Large-Precat :
  {αC : Level → Level} {βC : Level → Level → Level} →
  (C : Large-Precat αC βC) →
  {l1 l2 l3 l4 : Level} →
  {A : obj-Large-Precat C l1} {B : obj-Large-Precat C l2} →
  {X : obj-Large-Precat C l3} {Y : obj-Large-Precat C l4} →
  (top : type-hom-Large-Precat C A B) (left : type-hom-Large-Precat C A X) →
  (right : type-hom-Large-Precat C B Y) (bottom : type-hom-Large-Precat C X Y) →
  UU (βC l1 l4)
square-Large-Precat C top left right bottom =
  comp-hom-Large-Precat C bottom left ＝ comp-hom-Large-Precat C right top

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  (F : functor-Large-Precat C D γF) (G : functor-Large-Precat C D γG)
  where

  record natural-transformation-Large-Precat : UUω
    where
    constructor make-natural-transformation
    field
      obj-natural-transformation-Large-Precat :
        {l1 : Level} (X : obj-Large-Precat C l1) →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat F X)
          ( obj-functor-Large-Precat G X)
      coherence-square-natural-transformation-Large-Precat :
        {l1 l2 : Level} {X : obj-Large-Precat C l1}
        {Y : obj-Large-Precat C l2} (f : type-hom-Large-Precat C X Y) →
        square-Large-Precat D
          ( obj-natural-transformation-Large-Precat X)
          ( hom-functor-Large-Precat F f)
          ( hom-functor-Large-Precat G f)
          ( obj-natural-transformation-Large-Precat Y)

  open natural-transformation-Large-Precat public
```

## Examples

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
id-natural-transformation-Large-Precat :
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level} →
  {C : Large-Precat αC βC} {D : Large-Precat αD βD} →
  (F : functor-Large-Precat C D γF) → natural-transformation-Large-Precat F F
obj-natural-transformation-Large-Precat
  (id-natural-transformation-Large-Precat {D = D} F) X =
    id-hom-Large-Precat D
coherence-square-natural-transformation-Large-Precat
  (id-natural-transformation-Large-Precat {D = D} F) f =
    ( left-unit-law-comp-hom-Large-Precat D (hom-functor-Large-Precat F f)) ∙
    ( inv
      ( right-unit-law-comp-hom-Large-Precat D
        ( hom-functor-Large-Precat F f)))
```
