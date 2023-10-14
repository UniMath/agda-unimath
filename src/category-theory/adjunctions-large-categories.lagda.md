# Adjunctions between large categories

```agda
module category-theory.adjunctions-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-categories
open import category-theory.large-categories
open import category-theory.natural-transformations-functors-large-categories

open import foundation.commuting-squares-of-maps
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Let `C` and `D` be two [large categories](category-theory.large-categories.md).
Two [functors](category-theory.functors-large-categories.md) `F : C → D` and
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

### The predicate of being an adjoint pair of functors

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (F : functor-Large-Category C D γF)
  (G : functor-Large-Category D C γG)
  where

  record is-adjoint-pair-Large-Category : UUω
    where
    field
      equiv-is-adjoint-pair-Large-Category :
        {l1 l2 : Level} (X : obj-Large-Category C l1)
        (Y : obj-Large-Category D l2) →
        hom-Large-Category C X (obj-functor-Large-Category G Y) ≃
        hom-Large-Category D (obj-functor-Large-Category F X) Y
      naturality-equiv-is-adjoint-pair-Large-Category :
        { l1 l2 l3 l4 : Level}
        { X1 : obj-Large-Category C l1}
        { X2 : obj-Large-Category C l2}
        { Y1 : obj-Large-Category D l3}
        { Y2 : obj-Large-Category D l4}
        ( f : hom-Large-Category C X2 X1)
        ( g : hom-Large-Category D Y1 Y2) →
        coherence-square-maps
          ( map-equiv (equiv-is-adjoint-pair-Large-Category X1 Y1))
          ( λ h →
            comp-hom-Large-Category C
              ( comp-hom-Large-Category C
                ( hom-functor-Large-Category G g)
                ( h))
              ( f))
          ( λ h →
            comp-hom-Large-Category D
              ( comp-hom-Large-Category D g h)
              ( hom-functor-Large-Category F f))
          ( map-equiv (equiv-is-adjoint-pair-Large-Category X2 Y2))

  open is-adjoint-pair-Large-Category public

  map-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category C X (obj-functor-Large-Category G Y) →
    hom-Large-Category D (obj-functor-Large-Category F X) Y
  map-equiv-is-adjoint-pair-Large-Category H X Y =
    map-equiv (equiv-is-adjoint-pair-Large-Category H X Y)

  inv-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category D (obj-functor-Large-Category F X) Y ≃
    hom-Large-Category C X (obj-functor-Large-Category G Y)
  inv-equiv-is-adjoint-pair-Large-Category H X Y =
    inv-equiv (equiv-is-adjoint-pair-Large-Category H X Y)

  map-inv-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category D (obj-functor-Large-Category F X) Y →
    hom-Large-Category C X (obj-functor-Large-Category G Y)
  map-inv-equiv-is-adjoint-pair-Large-Category H X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Large-Category H X Y)

  naturality-inv-equiv-is-adjoint-pair-Large-Category :
    ( H : is-adjoint-pair-Large-Category)
    { l1 l2 l3 l4 : Level}
    { X1 : obj-Large-Category C l1}
    { X2 : obj-Large-Category C l2}
    { Y1 : obj-Large-Category D l3}
    { Y2 : obj-Large-Category D l4}
    ( f : hom-Large-Category C X2 X1)
    ( g : hom-Large-Category D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Large-Category H X1 Y1)
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-functor-Large-Category F f))
      ( λ h →
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C (hom-functor-Large-Category G g) h)
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Large-Category H X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Large-Category
    H {X1 = X1} {X2} {Y1} {Y2} f g =
    coherence-square-inv-horizontal
      ( equiv-is-adjoint-pair-Large-Category H X1 Y1)
      ( λ h →
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C
            ( hom-functor-Large-Category G g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-functor-Large-Category F f))
      ( equiv-is-adjoint-pair-Large-Category H X2 Y2)
      ( naturality-equiv-is-adjoint-pair-Large-Category H f g)
```

### The predicate of being a left adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (G : functor-Large-Category D C γG)
  (F : functor-Large-Category C D γF)
  where

  is-left-adjoint-functor-Large-Category : UUω
  is-left-adjoint-functor-Large-Category =
    is-adjoint-pair-Large-Category F G
```

### The predicate of being a right adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (F : functor-Large-Category C D γF)
  (G : functor-Large-Category D C γG)
  where

  is-right-adjoint-functor-Large-Category : UUω
  is-right-adjoint-functor-Large-Category =
    is-adjoint-pair-Large-Category F G
```

### Adjunctions of large precategories

```agda
module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  where

  record Adjunction-Large-Category : UUω where
    field
      level-left-adjoint-Adjunction-Large-Category :
        Level → Level
      left-adjoint-Adjunction-Large-Category :
        functor-Large-Category C D
          level-left-adjoint-Adjunction-Large-Category
      level-right-adjoint-Adjunction-Large-Category :
        Level → Level
      right-adjoint-Adjunction-Large-Category :
        functor-Large-Category D C
          level-right-adjoint-Adjunction-Large-Category
      is-adjoint-pair-Adjunction-Large-Category :
        is-adjoint-pair-Large-Category
          left-adjoint-Adjunction-Large-Category
          right-adjoint-Adjunction-Large-Category

  open Adjunction-Large-Category public

  obj-left-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category) {l : Level} →
    obj-Large-Category C l →
    obj-Large-Category D
      ( level-left-adjoint-Adjunction-Large-Category FG l)
  obj-left-adjoint-Adjunction-Large-Category FG =
    obj-functor-Large-Category
      ( left-adjoint-Adjunction-Large-Category FG)

  hom-left-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    {X : obj-Large-Category C l1}
    {Y : obj-Large-Category C l2} →
    hom-Large-Category C X Y →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category FG X)
      ( obj-left-adjoint-Adjunction-Large-Category FG Y)
  hom-left-adjoint-Adjunction-Large-Category FG =
    hom-functor-Large-Category
      ( left-adjoint-Adjunction-Large-Category FG)

  preserves-identity-left-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 : Level}
    (X : obj-Large-Category C l1) →
    hom-left-adjoint-Adjunction-Large-Category FG
      ( id-hom-Large-Category C {X = X}) ＝
    id-hom-Large-Category D
  preserves-identity-left-adjoint-Adjunction-Large-Category FG X =
    preserves-identity-functor-Large-Category
      ( left-adjoint-Adjunction-Large-Category FG)

  obj-right-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 : Level} →
    obj-Large-Category D l1 →
    obj-Large-Category C
      ( level-right-adjoint-Adjunction-Large-Category FG l1)
  obj-right-adjoint-Adjunction-Large-Category FG =
    obj-functor-Large-Category
      ( right-adjoint-Adjunction-Large-Category FG)

  hom-right-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    {X : obj-Large-Category D l1}
    {Y : obj-Large-Category D l2} →
    hom-Large-Category D X Y →
    hom-Large-Category C
      ( obj-right-adjoint-Adjunction-Large-Category FG X)
      ( obj-right-adjoint-Adjunction-Large-Category FG Y)
  hom-right-adjoint-Adjunction-Large-Category FG =
    hom-functor-Large-Category
      ( right-adjoint-Adjunction-Large-Category FG)

  preserves-identity-right-adjoint-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l : Level}
    (Y : obj-Large-Category D l) →
    hom-right-adjoint-Adjunction-Large-Category FG
      ( id-hom-Large-Category D {X = Y}) ＝
    id-hom-Large-Category C
  preserves-identity-right-adjoint-Adjunction-Large-Category FG Y =
    preserves-identity-functor-Large-Category
      ( right-adjoint-Adjunction-Large-Category FG)

  equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category FG Y) ≃
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category FG X)
      ( Y)
  equiv-is-adjoint-pair-Adjunction-Large-Category FG =
    equiv-is-adjoint-pair-Large-Category
      ( is-adjoint-pair-Adjunction-Large-Category FG)

  map-equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category FG Y) →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category FG X)
      ( Y)
  map-equiv-is-adjoint-pair-Adjunction-Large-Category FG =
    map-equiv-is-adjoint-pair-Large-Category
      ( left-adjoint-Adjunction-Large-Category FG)
      ( right-adjoint-Adjunction-Large-Category FG)
      ( is-adjoint-pair-Adjunction-Large-Category FG)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Category C l1}
    {X2 : obj-Large-Category C l2}
    {Y1 : obj-Large-Category D l3}
    {Y2 : obj-Large-Category D l4}
    (f : hom-Large-Category C X2 X1)
    (g : hom-Large-Category D Y1 Y2) →
    coherence-square-maps
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Category FG X1 Y1)
      ( λ h →
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C
            ( hom-right-adjoint-Adjunction-Large-Category FG g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-left-adjoint-Adjunction-Large-Category FG f))
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Category FG X2 Y2)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Category FG =
    naturality-equiv-is-adjoint-pair-Large-Category
      ( is-adjoint-pair-Adjunction-Large-Category FG)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category FG X)
      ( Y) ≃
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category FG Y)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Category FG X Y =
    inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Category FG X Y)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category FG X)
      ( Y) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category FG Y)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category FG X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Category FG X Y)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category)
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Category C l1}
    {X2 : obj-Large-Category C l2}
    {Y1 : obj-Large-Category D l3}
    {Y2 : obj-Large-Category D l4}
    (f : hom-Large-Category C X2 X1)
    (g : hom-Large-Category D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category FG X1 Y1)
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-left-adjoint-Adjunction-Large-Category FG f))
      ( λ h →
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C
            ( hom-right-adjoint-Adjunction-Large-Category FG g)
            ( h))
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category FG X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category FG =
    naturality-inv-equiv-is-adjoint-pair-Large-Category
      ( left-adjoint-Adjunction-Large-Category FG)
      ( right-adjoint-Adjunction-Large-Category FG)
      ( is-adjoint-pair-Adjunction-Large-Category FG)
```

### The unit of an adjunction

Given an adjoint pair `F ⊣ G`, we can construct a natural transformation
`η : id → G ∘ F` called the **unit** of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  where

  unit-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category C D) →
    natural-transformation-Large-Category
      ( id-functor-Large-Category)
      ( comp-functor-Large-Category
        ( right-adjoint-Adjunction-Large-Category FG)
        ( left-adjoint-Adjunction-Large-Category FG))
  hom-family-natural-transformation-Large-Category
    ( unit-Adjunction-Large-Category FG)
    ( X) =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG X
      ( obj-left-adjoint-Adjunction-Large-Category C D FG X)
      ( id-hom-Large-Category D)
  coherence-square-natural-transformation-Large-Category
    ( unit-Adjunction-Large-Category FG) {X = X} {Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Category C
            ( comp-hom-Large-Category C (η Y) f))) ∙
        ( ap
          ( comp-hom-Large-Category' C
            ( comp-hom-Large-Category C (η Y) f))
          ( inv
            ( preserves-identity-right-adjoint-Adjunction-Large-Category C D FG
              ( obj-left-adjoint-Adjunction-Large-Category C D FG Y)))) ∙
        ( inv
          ( associative-comp-hom-Large-Category C
            ( hom-right-adjoint-Adjunction-Large-Category C D FG
              ( id-hom-Large-Category D))
            ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category
              C D FG Y
              ( obj-left-adjoint-Adjunction-Large-Category C D FG Y)
              ( id-hom-Large-Category D))
            ( f))) ∙
        ( inv
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category
            C D FG f
            ( id-hom-Large-Category D)
            ( id-hom-Large-Category D))) ∙
        ( ap
          ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG X
            ( obj-left-adjoint-Adjunction-Large-Category C D FG Y))
          ( ( associative-comp-hom-Large-Category D
              ( id-hom-Large-Category D)
              ( id-hom-Large-Category D)
              ( hom-left-adjoint-Adjunction-Large-Category C D FG f)) ∙
            ( left-unit-law-comp-hom-Large-Category D
              ( comp-hom-Large-Category D
                ( id-hom-Large-Category D)
                ( hom-left-adjoint-Adjunction-Large-Category C D FG f))) ∙
            ( left-unit-law-comp-hom-Large-Category D
                ( hom-left-adjoint-Adjunction-Large-Category C D FG f)) ∙
            ( inv
                ( right-unit-law-comp-hom-Large-Category D
                  ( hom-left-adjoint-Adjunction-Large-Category C D FG f))) ∙
            ( inv
              ( right-unit-law-comp-hom-Large-Category D
                ( comp-hom-Large-Category D
                  ( hom-left-adjoint-Adjunction-Large-Category C D FG f)
                  ( id-hom-Large-Category D)))) ∙
            ( ap
              ( comp-hom-Large-Category D
                ( comp-hom-Large-Category D
                  ( hom-left-adjoint-Adjunction-Large-Category C D FG f)
                  ( id-hom-Large-Category D)))
              ( inv
                ( preserves-identity-left-adjoint-Adjunction-Large-Category
                  C D FG X)))) ∙
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category
            C D FG
            ( id-hom-Large-Category C)
            ( hom-left-adjoint-Adjunction-Large-Category C D FG f)
            ( id-hom-Large-Category D)) ∙
          ( right-unit-law-comp-hom-Large-Category C
            ( comp-hom-Large-Category C
              ( hom-right-adjoint-Adjunction-Large-Category C D FG
                ( hom-left-adjoint-Adjunction-Large-Category C D FG f))
              ( η X)))))
    where
    η :
      {l : Level} (X : obj-Large-Category C l) →
      hom-Large-Category C X
        ( obj-right-adjoint-Adjunction-Large-Category C D FG
          ( obj-left-adjoint-Adjunction-Large-Category C D FG X))
    η =
      hom-family-natural-transformation-Large-Category
        ( unit-Adjunction-Large-Category FG)
```

### The counit of an adjunction

Given an adjoint pair `F ⊣ G`, we can construct a natural transformation
`ε : F ∘ G → id` called the **counit** of the adjunction.

```agda
  counit-Adjunction-Large-Category :
    (FG : Adjunction-Large-Category C D) →
    natural-transformation-Large-Category
      ( comp-functor-Large-Category
        ( left-adjoint-Adjunction-Large-Category FG)
        ( right-adjoint-Adjunction-Large-Category FG))
      ( id-functor-Large-Category)
  hom-family-natural-transformation-Large-Category
    ( counit-Adjunction-Large-Category FG) Y =
    map-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG
      ( obj-right-adjoint-Adjunction-Large-Category C D FG Y)
      ( Y)
      ( id-hom-Large-Category C)
  coherence-square-natural-transformation-Large-Category
    (counit-Adjunction-Large-Category FG) {X = X} {Y = Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Category D
            ( comp-hom-Large-Category D
              ( ε Y)
              ( hom-left-adjoint-Adjunction-Large-Category C D FG
                ( hom-right-adjoint-Adjunction-Large-Category C D FG f))))) ∙
        ( inv
          ( associative-comp-hom-Large-Category D
            ( id-hom-Large-Category D)
            ( map-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG
              ( obj-right-adjoint-Adjunction-Large-Category C D FG Y)
              ( Y)
              ( id-hom-Large-Category C))
            ( hom-left-adjoint-Adjunction-Large-Category C D FG
              ( hom-right-adjoint-Adjunction-Large-Category C D FG f)))) ∙
        ( inv
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG
            ( hom-right-adjoint-Adjunction-Large-Category C D FG f)
            ( id-hom-Large-Category D)
            ( id-hom-Large-Category C))) ∙
        ( ap
          ( map-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG
            ( obj-right-adjoint-Adjunction-Large-Category C D FG X)
            ( Y))
          ( ( ap
              ( comp-hom-Large-Category' C
                ( hom-right-adjoint-Adjunction-Large-Category C D FG f))
              ( ( right-unit-law-comp-hom-Large-Category C
                  ( hom-right-adjoint-Adjunction-Large-Category C D FG
                    ( id-hom-Large-Category D))) ∙
                ( preserves-identity-right-adjoint-Adjunction-Large-Category
                    C D FG Y))) ∙
            ( left-unit-law-comp-hom-Large-Category C
              ( hom-right-adjoint-Adjunction-Large-Category C D FG f)) ∙
            ( ( inv
                ( right-unit-law-comp-hom-Large-Category C
                  ( hom-right-adjoint-Adjunction-Large-Category C D FG f))) ∙
              ( inv
                ( right-unit-law-comp-hom-Large-Category C
                  ( comp-hom-Large-Category C
                    ( hom-right-adjoint-Adjunction-Large-Category C D FG f)
                    ( id-hom-Large-Category C)))))) ∙
        ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Category C D FG
            ( id-hom-Large-Category C)
            ( f)
            ( id-hom-Large-Category C)) ∙
          ( ap
            ( comp-hom-Large-Category
              ( D)
              ( comp-hom-Large-Category D f (ε X)))
            ( preserves-identity-left-adjoint-Adjunction-Large-Category C D FG
              ( obj-right-adjoint-Adjunction-Large-Category C D FG X))) ∙
          ( right-unit-law-comp-hom-Large-Category D
            ( comp-hom-Large-Category D f (ε X)))))
    where
    ε :
      {l : Level} (Y : obj-Large-Category D l) →
      hom-Large-Category D
        ( obj-left-adjoint-Adjunction-Large-Category C D FG
          ( obj-right-adjoint-Adjunction-Large-Category C D FG Y))
        ( Y)
    ε =
      hom-family-natural-transformation-Large-Category
        ( counit-Adjunction-Large-Category FG)
```
