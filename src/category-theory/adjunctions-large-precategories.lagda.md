# Adjunctions between large precategories

```agda
module category-theory.adjunctions-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Let `C` and `D` be two
[large precategories](category-theory.large-precategories.md). Two
[functors](category-theory.functors-large-precategories.md) `F : C → D` and
`G : D → C` constitute an **adjoint pair** if

- for each pair of objects `X` in `C` and `Y` in `D`, there is an
  [equivalence](foundation-core.equivalences.md)
  `ϕ X Y : hom X (G Y) ≃ hom (F X) Y` such that
- for every pair of morhpisms `f : X₂ → X₁` and `g : Y₁ → Y₂` the following
  square commutes:

```text
                       ϕ X₁ Y₁
       hom X₁ (G Y₁) --------> hom (F X₁) Y₁
            |                        |
G g ∘ _ ∘ f |                        | g ∘ _ ∘ F f
            |                        |
            v                        v
       hom X₂ (G Y₂) --------> hom (F X₂) Y₂
                       ϕ X₂ Y₂
```

In this case we say that `F` is **left adjoint** to `G` and `G` is **right
adjoint** to `F` and write this as `F ⊣ G`.

## Definition

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF)
  (G : functor-Large-Precategory D C γG)
  where

  record is-adjoint-pair-Large-Precategory : UUω
    where
    field
      equiv-is-adjoint-pair-Large-Precategory :
        {l1 l2 : Level} (X : obj-Large-Precategory C l1)
        (Y : obj-Large-Precategory D l2) →
        ( hom-Large-Precategory C
          ( X)
          ( obj-functor-Large-Precategory G Y)) ≃
        ( hom-Large-Precategory D
          ( obj-functor-Large-Precategory F X)
          ( Y))
      naturality-equiv-is-adjoint-pair-Large-Precategory :
        { l1 l2 l3 l4 : Level}
        { X1 : obj-Large-Precategory C l1}
        { X2 : obj-Large-Precategory C l2}
        { Y1 : obj-Large-Precategory D l3}
        { Y2 : obj-Large-Precategory D l4}
        ( f : hom-Large-Precategory C X2 X1)
        ( g : hom-Large-Precategory D Y1 Y2) →
        coherence-square-maps
          ( map-equiv (equiv-is-adjoint-pair-Large-Precategory X1 Y1))
          ( λ h →
            comp-hom-Large-Precategory C
              ( comp-hom-Large-Precategory C
                ( hom-functor-Large-Precategory G g)
                ( h))
              ( f))
          ( λ h →
            comp-hom-Large-Precategory D
              ( comp-hom-Large-Precategory D g h)
              ( hom-functor-Large-Precategory F f))
          ( map-equiv (equiv-is-adjoint-pair-Large-Precategory X2 Y2))

  open is-adjoint-pair-Large-Precategory public

  map-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory) {l1 l2 : Level}
    (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory D l2) →
    ( hom-Large-Precategory C X (obj-functor-Large-Precategory G Y)) →
    ( hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y)
  map-equiv-is-adjoint-pair-Large-Precategory H X Y =
    map-equiv (equiv-is-adjoint-pair-Large-Precategory H X Y)

  inv-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory)
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y ≃
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y)
  inv-equiv-is-adjoint-pair-Large-Precategory H X Y =
    inv-equiv (equiv-is-adjoint-pair-Large-Precategory H X Y)

  map-inv-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory) {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y →
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y)
  map-inv-equiv-is-adjoint-pair-Large-Precategory H X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Large-Precategory H X Y)

  naturality-inv-equiv-is-adjoint-pair-Large-Precategory :
    ( H : is-adjoint-pair-Large-Precategory)
    { l1 l2 l3 l4 : Level}
    { X1 : obj-Large-Precategory C l1}
    { X2 : obj-Large-Precategory C l2}
    { Y1 : obj-Large-Precategory D l3}
    { Y2 : obj-Large-Precategory D l4}
    ( f : hom-Large-Precategory C X2 X1)
    ( g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Large-Precategory H X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-functor-Large-Precategory F f))
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C (hom-functor-Large-Precategory G g) h)
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Large-Precategory H X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Large-Precategory
    H {X1 = X1} {X2} {Y1} {Y2} f g =
    coherence-square-inv-horizontal
      ( equiv-is-adjoint-pair-Large-Precategory H X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-functor-Large-Precategory G g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-functor-Large-Precategory F f))
      ( equiv-is-adjoint-pair-Large-Precategory H X2 Y2)
      ( naturality-equiv-is-adjoint-pair-Large-Precategory H f g)

module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (G : functor-Large-Precategory D C γG)
  (F : functor-Large-Precategory C D γF)
  where

  is-left-adjoint-functor-Large-Precategory : UUω
  is-left-adjoint-functor-Large-Precategory =
    is-adjoint-pair-Large-Precategory F G

module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF)
  (G : functor-Large-Precategory D C γG)
  where

  is-right-adjoint-functor-Large-Precategory : UUω
  is-right-adjoint-functor-Large-Precategory =
    is-adjoint-pair-Large-Precategory F G

module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  where

  record Adjunction-Large-Precategory : UUω where
    field
      level-left-adjoint-Adjunction-Large-Precategory :
        Level → Level
      left-adjoint-Adjunction-Large-Precategory :
        functor-Large-Precategory C D
          level-left-adjoint-Adjunction-Large-Precategory
      level-right-adjoint-Adjunction-Large-Precategory :
        Level → Level
      right-adjoint-Adjunction-Large-Precategory :
        functor-Large-Precategory D C
          level-right-adjoint-Adjunction-Large-Precategory
      is-adjoint-pair-Adjunction-Large-Precategory :
        is-adjoint-pair-Large-Precategory
          left-adjoint-Adjunction-Large-Precategory
          right-adjoint-Adjunction-Large-Precategory

  open Adjunction-Large-Precategory public

  obj-left-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory) {l : Level} →
    obj-Large-Precategory C l →
    obj-Large-Precategory D
      ( level-left-adjoint-Adjunction-Large-Precategory FG l)
  obj-left-adjoint-Adjunction-Large-Precategory FG =
    obj-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  hom-left-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2} →
    hom-Large-Precategory C X Y →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory FG X)
      ( obj-left-adjoint-Adjunction-Large-Precategory FG Y)
  hom-left-adjoint-Adjunction-Large-Precategory FG =
    hom-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  preserves-id-left-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 : Level}
    (X : obj-Large-Precategory C l1) →
    hom-left-adjoint-Adjunction-Large-Precategory FG
      ( id-hom-Large-Precategory C {X = X}) ＝
    id-hom-Large-Precategory D
  preserves-id-left-adjoint-Adjunction-Large-Precategory FG X =
    preserves-id-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  obj-right-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 : Level} →
    obj-Large-Precategory D l1 →
    obj-Large-Precategory C
      ( level-right-adjoint-Adjunction-Large-Precategory FG l1)
  obj-right-adjoint-Adjunction-Large-Precategory FG =
    obj-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  hom-right-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    {X : obj-Large-Precategory D l1}
    {Y : obj-Large-Precategory D l2} →
    hom-Large-Precategory D X Y →
    hom-Large-Precategory C
      ( obj-right-adjoint-Adjunction-Large-Precategory FG X)
      ( obj-right-adjoint-Adjunction-Large-Precategory FG Y)
  hom-right-adjoint-Adjunction-Large-Precategory FG =
    hom-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  preserves-id-right-adjoint-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l : Level}
    (Y : obj-Large-Precategory D l) →
    hom-right-adjoint-Adjunction-Large-Precategory FG
      ( id-hom-Large-Precategory D {X = Y}) ＝
    id-hom-Large-Precategory C
  preserves-id-right-adjoint-Adjunction-Large-Precategory FG Y =
    preserves-id-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory FG Y) ≃
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory FG X)
      ( Y)
  equiv-is-adjoint-pair-Adjunction-Large-Precategory FG =
    equiv-is-adjoint-pair-Large-Precategory
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  map-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory FG Y) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory FG X)
      ( Y)
  map-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG =
    map-equiv-is-adjoint-pair-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)
      ( right-adjoint-Adjunction-Large-Precategory FG)
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precategory C l1}
    {X2 : obj-Large-Precategory C l2}
    {Y1 : obj-Large-Precategory D l3}
    {Y2 : obj-Large-Precategory D l4}
    (f : hom-Large-Precategory C X2 X1)
    (g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory FG g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-left-adjoint-Adjunction-Large-Precategory FG f))
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X2 Y2)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG =
    naturality-equiv-is-adjoint-pair-Large-Precategory
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory FG X)
      ( Y) ≃
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory FG Y)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X Y =
    inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X Y)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory FG X)
      ( Y) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory FG Y)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X Y)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory)
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precategory C l1}
    {X2 : obj-Large-Precategory C l2}
    {Y1 : obj-Large-Precategory D l3}
    {Y2 : obj-Large-Precategory D l4}
    (f : hom-Large-Precategory C X2 X1)
    (g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-left-adjoint-Adjunction-Large-Precategory FG f))
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory FG g)
            ( h))
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory FG =
    naturality-inv-equiv-is-adjoint-pair-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)
      ( right-adjoint-Adjunction-Large-Precategory FG)
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)
```

## Properties

### Unit of adjunction

Given an adjoint pair `F ⊣ G`, we can construct a natural transformation
`η : id → G ∘ F` called the unit of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  where

  unit-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory C D) →
    natural-transformation-Large-Precategory
      ( id-functor-Large-Precategory)
      ( comp-functor-Large-Precategory
        ( right-adjoint-Adjunction-Large-Precategory FG)
        ( left-adjoint-Adjunction-Large-Precategory FG))
  hom-family-natural-transformation-Large-Precategory
    ( unit-Adjunction-Large-Precategory FG)
    ( X) =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG X
      ( obj-left-adjoint-Adjunction-Large-Precategory C D FG X)
      ( id-hom-Large-Precategory D)
  coherence-square-natural-transformation-Large-Precategory
    ( unit-Adjunction-Large-Precategory FG) {X = X} {Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Precategory C
            ( comp-hom-Large-Precategory C (η Y) f))) ∙
        ( ap
          ( comp-hom-Large-Precategory' C
            ( comp-hom-Large-Precategory C (η Y) f))
          ( inv
            ( preserves-id-right-adjoint-Adjunction-Large-Precategory C D FG
              ( obj-left-adjoint-Adjunction-Large-Precategory C D FG Y)))) ∙
        ( inv
          ( associative-comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory C D FG
              ( id-hom-Large-Precategory D))
            ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
              C D FG Y
              ( obj-left-adjoint-Adjunction-Large-Precategory C D FG Y)
              ( id-hom-Large-Precategory D))
            ( f))) ∙
        ( inv
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
            C D FG f
            ( id-hom-Large-Precategory D)
            ( id-hom-Large-Precategory D))) ∙
        ( ap
          ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG X
            ( obj-left-adjoint-Adjunction-Large-Precategory C D FG Y))
          ( ( associative-comp-hom-Large-Precategory D
              ( id-hom-Large-Precategory D)
              ( id-hom-Large-Precategory D)
              ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)) ∙
            ( left-unit-law-comp-hom-Large-Precategory D
              ( comp-hom-Large-Precategory D
                ( id-hom-Large-Precategory D)
                ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f))) ∙
            ( left-unit-law-comp-hom-Large-Precategory D
                ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)) ∙
            ( inv
                ( right-unit-law-comp-hom-Large-Precategory D
                  ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f))) ∙
            ( inv
              ( right-unit-law-comp-hom-Large-Precategory D
                ( comp-hom-Large-Precategory D
                  ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)
                  ( id-hom-Large-Precategory D)))) ∙
            ( ap
              ( comp-hom-Large-Precategory D
                ( comp-hom-Large-Precategory D
                  ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)
                  ( id-hom-Large-Precategory D)))
              ( inv
                ( preserves-id-left-adjoint-Adjunction-Large-Precategory
                  C D FG X)))) ∙
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
            C D FG
            ( id-hom-Large-Precategory C)
            ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)
            ( id-hom-Large-Precategory D)) ∙
          ( right-unit-law-comp-hom-Large-Precategory C
            ( comp-hom-Large-Precategory C
              ( hom-right-adjoint-Adjunction-Large-Precategory C D FG
                ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f))
              ( η X)))))
    where
    η :
      {l : Level} (X : obj-Large-Precategory C l) →
      hom-Large-Precategory C X
        ( obj-right-adjoint-Adjunction-Large-Precategory C D FG
          ( obj-left-adjoint-Adjunction-Large-Precategory C D FG X))
    η =
      hom-family-natural-transformation-Large-Precategory
        ( unit-Adjunction-Large-Precategory FG)
```

### Counit of adjunction

Given an adjoint pair `F ⊣ G`, we can construct a natural transformation
`ε : F ∘ G → id` called the counit of the adjunction.

```agda
  counit-Adjunction-Large-Precategory :
    (FG : Adjunction-Large-Precategory C D) →
    natural-transformation-Large-Precategory
      ( comp-functor-Large-Precategory
        ( left-adjoint-Adjunction-Large-Precategory FG)
        ( right-adjoint-Adjunction-Large-Precategory FG))
      ( id-functor-Large-Precategory)
  hom-family-natural-transformation-Large-Precategory
    ( counit-Adjunction-Large-Precategory FG) Y =
    map-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
      ( obj-right-adjoint-Adjunction-Large-Precategory C D FG Y)
      ( Y)
      ( id-hom-Large-Precategory C)
  coherence-square-natural-transformation-Large-Precategory
    (counit-Adjunction-Large-Precategory FG) {X = X} {Y = Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Precategory D
            ( comp-hom-Large-Precategory D
              ( ε Y)
              ( hom-left-adjoint-Adjunction-Large-Precategory C D FG
                ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f))))) ∙
        ( inv
          ( associative-comp-hom-Large-Precategory D
            ( id-hom-Large-Precategory D)
            ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
              ( obj-right-adjoint-Adjunction-Large-Precategory C D FG Y)
              ( Y)
              ( id-hom-Large-Precategory C))
            ( hom-left-adjoint-Adjunction-Large-Precategory C D FG
              ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)))) ∙
        ( inv
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
            ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)
            ( id-hom-Large-Precategory D)
            ( id-hom-Large-Precategory C))) ∙
        ( ap
          ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
            ( obj-right-adjoint-Adjunction-Large-Precategory C D FG X)
            ( Y))
          ( ( ap
              ( comp-hom-Large-Precategory' C
                ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f))
              ( ( right-unit-law-comp-hom-Large-Precategory C
                  ( hom-right-adjoint-Adjunction-Large-Precategory C D FG
                    ( id-hom-Large-Precategory D))) ∙
                ( preserves-id-right-adjoint-Adjunction-Large-Precategory
                    C D FG Y))) ∙
            ( left-unit-law-comp-hom-Large-Precategory C
              ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)) ∙
            ( ( inv
                ( right-unit-law-comp-hom-Large-Precategory C
                  ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f))) ∙
              ( inv
                ( right-unit-law-comp-hom-Large-Precategory C
                  ( comp-hom-Large-Precategory C
                    ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)
                    ( id-hom-Large-Precategory C)))))) ∙
        ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
            ( id-hom-Large-Precategory C)
            ( f)
            ( id-hom-Large-Precategory C)) ∙
          ( ap
            ( comp-hom-Large-Precategory
              ( D)
              ( comp-hom-Large-Precategory D f (ε X)))
            ( preserves-id-left-adjoint-Adjunction-Large-Precategory C D FG
              ( obj-right-adjoint-Adjunction-Large-Precategory C D FG X))) ∙
          ( right-unit-law-comp-hom-Large-Precategory D
            ( comp-hom-Large-Precategory D f (ε X)))))
    where
    ε :
      {l : Level} (Y : obj-Large-Precategory D l) →
      hom-Large-Precategory D
        ( obj-left-adjoint-Adjunction-Large-Precategory C D FG
          ( obj-right-adjoint-Adjunction-Large-Precategory C D FG Y))
        ( Y)
    ε =
      hom-family-natural-transformation-Large-Precategory
        ( counit-Adjunction-Large-Precategory FG)
```
