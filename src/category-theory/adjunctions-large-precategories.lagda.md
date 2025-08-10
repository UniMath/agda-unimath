# Adjunctions between large precategories

```agda
module category-theory.adjunctions-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-large-precategories

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
  `ϕ X Y : hom (F X) Y ≃ hom X (G Y)` such that
- for every pair of morphisms `f : X₂ → X₁` and `g : Y₁ → Y₂` the following
  square commutes:

```text
                       ϕ X₁ Y₁
        hom (F X₁) Y₁ --------> hom X₁ (G Y₁)
              |                       |
  g ∘ - ∘ F f |                       | G g ∘ - ∘ f
              |                       |
              ∨                       ∨
        hom (F X₂) Y₂ --------> hom X₂ (G Y₂)
                       ϕ X₂ Y₂
```

In this case we say that `F` is **left adjoint** to `G` and `G` is **right
adjoint** to `F`, and write this as `F ⊣ G`.

**Note:** The direction of the equivalence `ϕ X Y` is chosen in such a way that
it often coincides with the direction of the natural map. For example, in the
[abelianization adjunction](group-theory.abelianization-groups.md), the natural
candidate for an equivalence is given by precomposition

```text
  - ∘ η : hom (abelianization-Group G) A → hom G (group-Ab A)
```

by the unit of the adjunction.

## Definition

### The predicate of being an adjoint pair of functors

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG D C)
  where

  family-of-equivalences-adjoint-pair-Large-Precategory : UUω
  family-of-equivalences-adjoint-pair-Large-Precategory =
    {l1 l2 : Level} (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y ≃
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y)

  naturality-family-of-equivalences-adjoint-pair-Large-Precategory :
    family-of-equivalences-adjoint-pair-Large-Precategory → UUω
  naturality-family-of-equivalences-adjoint-pair-Large-Precategory e =
    { l1 l2 l3 l4 : Level}
    { X1 : obj-Large-Precategory C l1}
    { X2 : obj-Large-Precategory C l2}
    { Y1 : obj-Large-Precategory D l3}
    { Y2 : obj-Large-Precategory D l4}
    ( f : hom-Large-Precategory C X2 X1)
    ( g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-equiv (e X1 Y1))
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-functor-Large-Precategory F f))
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-functor-Large-Precategory G g)
            ( h))
          ( f))
      ( map-equiv (e X2 Y2))

  record is-adjoint-pair-Large-Precategory : UUω
    where
    field
      equiv-is-adjoint-pair-Large-Precategory :
        family-of-equivalences-adjoint-pair-Large-Precategory
      naturality-equiv-is-adjoint-pair-Large-Precategory :
        naturality-family-of-equivalences-adjoint-pair-Large-Precategory
          equiv-is-adjoint-pair-Large-Precategory

  open is-adjoint-pair-Large-Precategory public

  map-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory) {l1 l2 : Level}
    (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y →
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y)
  map-equiv-is-adjoint-pair-Large-Precategory H X Y =
    map-equiv (equiv-is-adjoint-pair-Large-Precategory H X Y)

  inv-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory) {l1 l2 : Level}
    (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y) ≃
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y
  inv-equiv-is-adjoint-pair-Large-Precategory H X Y =
    inv-equiv (equiv-is-adjoint-pair-Large-Precategory H X Y)

  map-inv-equiv-is-adjoint-pair-Large-Precategory :
    (H : is-adjoint-pair-Large-Precategory) {l1 l2 : Level}
    (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C X (obj-functor-Large-Precategory G Y) →
    hom-Large-Precategory D (obj-functor-Large-Precategory F X) Y
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
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C (hom-functor-Large-Precategory G g) h)
          ( f))
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-functor-Large-Precategory F f))
      ( map-inv-equiv-is-adjoint-pair-Large-Precategory H X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Large-Precategory
    H {X1 = X1} {X2} {Y1} {Y2} f g =
    horizontal-inv-equiv-coherence-square-maps
      ( equiv-is-adjoint-pair-Large-Precategory H X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-functor-Large-Precategory F f))
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-functor-Large-Precategory G g)
            ( h))
          ( f))
      ( equiv-is-adjoint-pair-Large-Precategory H X2 Y2)
      ( naturality-equiv-is-adjoint-pair-Large-Precategory H f g)
```

### The predicate of being a left adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (G : functor-Large-Precategory γG D C)
  (F : functor-Large-Precategory γF C D)
  where

  is-left-adjoint-functor-Large-Precategory : UUω
  is-left-adjoint-functor-Large-Precategory =
    is-adjoint-pair-Large-Precategory C D F G
```

### The predicate of being a right adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG D C)
  where

  is-right-adjoint-functor-Large-Precategory : UUω
  is-right-adjoint-functor-Large-Precategory =
    is-adjoint-pair-Large-Precategory C D F G
```

### Adjunctions of large precategories

```agda
module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  (γ δ : Level → Level)
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  where

  record Adjunction-Large-Precategory : UUω where
    field
      left-adjoint-Adjunction-Large-Precategory :
        functor-Large-Precategory γ C D
      right-adjoint-Adjunction-Large-Precategory :
        functor-Large-Precategory δ D C
      is-adjoint-pair-Adjunction-Large-Precategory :
        is-adjoint-pair-Large-Precategory C D
          left-adjoint-Adjunction-Large-Precategory
          right-adjoint-Adjunction-Large-Precategory

  open Adjunction-Large-Precategory public

module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  {γ δ : Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (FG : Adjunction-Large-Precategory γ δ C D)
  where

  obj-left-adjoint-Adjunction-Large-Precategory :
    {l : Level} → obj-Large-Precategory C l → obj-Large-Precategory D (γ l)
  obj-left-adjoint-Adjunction-Large-Precategory =
    obj-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  hom-left-adjoint-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2} →
    hom-Large-Precategory C X Y →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory X)
      ( obj-left-adjoint-Adjunction-Large-Precategory Y)
  hom-left-adjoint-Adjunction-Large-Precategory =
    hom-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  preserves-id-left-adjoint-Adjunction-Large-Precategory :
    {l1 : Level} (X : obj-Large-Precategory C l1) →
    hom-left-adjoint-Adjunction-Large-Precategory
      ( id-hom-Large-Precategory C {X = X}) ＝
    id-hom-Large-Precategory D
  preserves-id-left-adjoint-Adjunction-Large-Precategory X =
    preserves-id-functor-Large-Precategory
      ( left-adjoint-Adjunction-Large-Precategory FG)

  obj-right-adjoint-Adjunction-Large-Precategory :
    {l1 : Level} → obj-Large-Precategory D l1 → obj-Large-Precategory C (δ l1)
  obj-right-adjoint-Adjunction-Large-Precategory =
    obj-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  hom-right-adjoint-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Precategory D l1}
    {Y : obj-Large-Precategory D l2} →
    hom-Large-Precategory D X Y →
    hom-Large-Precategory C
      ( obj-right-adjoint-Adjunction-Large-Precategory X)
      ( obj-right-adjoint-Adjunction-Large-Precategory Y)
  hom-right-adjoint-Adjunction-Large-Precategory =
    hom-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  preserves-id-right-adjoint-Adjunction-Large-Precategory :
    {l : Level}
    (Y : obj-Large-Precategory D l) →
    hom-right-adjoint-Adjunction-Large-Precategory
      ( id-hom-Large-Precategory D {X = Y}) ＝
    id-hom-Large-Precategory C
  preserves-id-right-adjoint-Adjunction-Large-Precategory Y =
    preserves-id-functor-Large-Precategory
      ( right-adjoint-Adjunction-Large-Precategory FG)

  equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory X)
      ( Y) ≃
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory Y)
  equiv-is-adjoint-pair-Adjunction-Large-Precategory =
    equiv-is-adjoint-pair-Large-Precategory
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  map-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory X)
      ( Y) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory Y)
  map-equiv-is-adjoint-pair-Adjunction-Large-Precategory =
    map-equiv-is-adjoint-pair-Large-Precategory C D
      ( left-adjoint-Adjunction-Large-Precategory FG)
      ( right-adjoint-Adjunction-Large-Precategory FG)
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precategory C l1}
    {X2 : obj-Large-Precategory C l2}
    {Y1 : obj-Large-Precategory D l3}
    {Y2 : obj-Large-Precategory D l4}
    (f : hom-Large-Precategory C X2 X1)
    (g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-left-adjoint-Adjunction-Large-Precategory f))
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory g)
            ( h))
          ( f))
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory X2 Y2)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory =
    naturality-equiv-is-adjoint-pair-Large-Precategory
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory Y) ≃
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory X)
      ( Y)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory X Y =
    inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Precategory X Y)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1)
    (Y : obj-Large-Precategory D l2) →
    hom-Large-Precategory C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Precategory Y) →
    hom-Large-Precategory D
      ( obj-left-adjoint-Adjunction-Large-Precategory X)
      ( Y)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Adjunction-Large-Precategory X Y)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precategory C l1}
    {X2 : obj-Large-Precategory C l2}
    {Y1 : obj-Large-Precategory D l3}
    {Y2 : obj-Large-Precategory D l4}
    (f : hom-Large-Precategory C X2 X1)
    (g : hom-Large-Precategory D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory X1 Y1)
      ( λ h →
        comp-hom-Large-Precategory C
          ( comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Precategory D
          ( comp-hom-Large-Precategory D g h)
          ( hom-left-adjoint-Adjunction-Large-Precategory f))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory =
    naturality-inv-equiv-is-adjoint-pair-Large-Precategory C D
      ( left-adjoint-Adjunction-Large-Precategory FG)
      ( right-adjoint-Adjunction-Large-Precategory FG)
      ( is-adjoint-pair-Adjunction-Large-Precategory FG)
```

### The unit of an adjunction

Given an adjoint pair `F ⊣ G`, we construct a natural transformation
`η : id → G ∘ F` called the **unit** of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} {γ δ : Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  (FG : Adjunction-Large-Precategory γ δ C D)
  where

  hom-unit-Adjunction-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C C
      ( id-functor-Large-Precategory C)
      ( comp-functor-Large-Precategory C D C
        ( right-adjoint-Adjunction-Large-Precategory FG)
        ( left-adjoint-Adjunction-Large-Precategory FG))
  hom-unit-Adjunction-Large-Precategory X =
    map-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG X
      ( obj-left-adjoint-Adjunction-Large-Precategory C D FG X)
      ( id-hom-Large-Precategory D)

  naturality-unit-Adjunction-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C C
      ( id-functor-Large-Precategory C)
      ( comp-functor-Large-Precategory C D C
        ( right-adjoint-Adjunction-Large-Precategory FG)
        ( left-adjoint-Adjunction-Large-Precategory FG))
      ( hom-unit-Adjunction-Large-Precategory)
  naturality-unit-Adjunction-Large-Precategory {X = X} {Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Precategory C
            ( comp-hom-Large-Precategory C
              ( hom-unit-Adjunction-Large-Precategory
                ( Y))
              ( f)))) ∙
        ( ap
          ( comp-hom-Large-Precategory' C
            ( comp-hom-Large-Precategory C
              ( hom-unit-Adjunction-Large-Precategory
                ( Y))
              ( f)))
          ( inv
            ( preserves-id-right-adjoint-Adjunction-Large-Precategory
              ( C)
              ( D)
              ( FG)
              ( obj-left-adjoint-Adjunction-Large-Precategory C D FG Y)))) ∙
        ( inv
          ( associative-comp-hom-Large-Precategory C
            ( hom-right-adjoint-Adjunction-Large-Precategory C D FG
              ( id-hom-Large-Precategory D))
            ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory
              C D FG Y
              ( obj-left-adjoint-Adjunction-Large-Precategory C D FG Y)
              ( id-hom-Large-Precategory D))
            ( f))) ∙
        ( inv
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory
            C D FG f
            ( id-hom-Large-Precategory D)
            ( id-hom-Large-Precategory D))) ∙
        ( ap
          ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG X
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
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory
            C D FG
            ( id-hom-Large-Precategory C)
            ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f)
            ( id-hom-Large-Precategory D)) ∙
          ( right-unit-law-comp-hom-Large-Precategory C
            ( comp-hom-Large-Precategory C
              ( hom-right-adjoint-Adjunction-Large-Precategory C D FG
                ( hom-left-adjoint-Adjunction-Large-Precategory C D FG f))
              ( hom-unit-Adjunction-Large-Precategory
                ( X))))))

  unit-Adjunction-Large-Precategory :
    natural-transformation-Large-Precategory C C
      ( id-functor-Large-Precategory C)
      ( comp-functor-Large-Precategory C D C
        ( right-adjoint-Adjunction-Large-Precategory FG)
        ( left-adjoint-Adjunction-Large-Precategory FG))
  hom-natural-transformation-Large-Precategory
    unit-Adjunction-Large-Precategory =
    hom-unit-Adjunction-Large-Precategory
  naturality-natural-transformation-Large-Precategory
    unit-Adjunction-Large-Precategory =
    naturality-unit-Adjunction-Large-Precategory
```

### The counit of an adjunction

Given an adjoint pair `F ⊣ G`, we construct a natural transformation
`ε : F ∘ G → id` called the **counit** of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} {γ δ : Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  (FG : Adjunction-Large-Precategory γ δ C D)
  where

  hom-counit-Adjunction-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory D D
      ( comp-functor-Large-Precategory D C D
        ( left-adjoint-Adjunction-Large-Precategory FG)
        ( right-adjoint-Adjunction-Large-Precategory FG))
      ( id-functor-Large-Precategory D)
  hom-counit-Adjunction-Large-Precategory Y =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
      ( obj-right-adjoint-Adjunction-Large-Precategory C D FG Y)
      ( Y)
      ( id-hom-Large-Precategory C)

  naturality-counit-Adjunction-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory D D
      ( comp-functor-Large-Precategory D C D
        ( left-adjoint-Adjunction-Large-Precategory FG)
        ( right-adjoint-Adjunction-Large-Precategory FG))
      ( id-functor-Large-Precategory D)
      ( hom-counit-Adjunction-Large-Precategory)
  naturality-counit-Adjunction-Large-Precategory {X = X} {Y = Y} f =
    inv
      ( ( inv
          ( left-unit-law-comp-hom-Large-Precategory D
            ( comp-hom-Large-Precategory D
              ( hom-counit-Adjunction-Large-Precategory
                ( Y))
              ( hom-left-adjoint-Adjunction-Large-Precategory C D FG
                ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f))))) ∙
        ( inv
          ( associative-comp-hom-Large-Precategory D
            ( id-hom-Large-Precategory D)
            ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
              ( obj-right-adjoint-Adjunction-Large-Precategory C D FG Y)
              ( Y)
              ( id-hom-Large-Precategory C))
            ( hom-left-adjoint-Adjunction-Large-Precategory C D FG
              ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)))) ∙
        ( inv
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
            ( C)
            ( D)
            ( FG)
            ( hom-right-adjoint-Adjunction-Large-Precategory C D FG f)
            ( id-hom-Large-Precategory D)
            ( id-hom-Large-Precategory C))) ∙
        ( ap
          ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D FG
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
        ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory C D
          ( FG)
          ( id-hom-Large-Precategory C)
            ( f)
            ( id-hom-Large-Precategory C)) ∙
          ( ap
            ( comp-hom-Large-Precategory
              ( D)
              ( comp-hom-Large-Precategory D f
                ( hom-counit-Adjunction-Large-Precategory
                  ( X))))
            ( preserves-id-left-adjoint-Adjunction-Large-Precategory
              ( C)
              ( D)
              ( FG)
              ( obj-right-adjoint-Adjunction-Large-Precategory C D FG X))) ∙
          ( right-unit-law-comp-hom-Large-Precategory D
            ( comp-hom-Large-Precategory D f
              ( hom-counit-Adjunction-Large-Precategory
                ( X))))))

  counit-Adjunction-Large-Precategory :
    natural-transformation-Large-Precategory D D
      ( comp-functor-Large-Precategory D C D
        ( left-adjoint-Adjunction-Large-Precategory FG)
        ( right-adjoint-Adjunction-Large-Precategory FG))
      ( id-functor-Large-Precategory D)
  hom-natural-transformation-Large-Precategory
    counit-Adjunction-Large-Precategory =
    hom-counit-Adjunction-Large-Precategory
  naturality-natural-transformation-Large-Precategory
    counit-Adjunction-Large-Precategory =
    naturality-counit-Adjunction-Large-Precategory
```
