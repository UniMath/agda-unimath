# Adjunctions between large categories

```agda
module category-theory.adjunctions-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-large-precategories
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
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG D C)
  where

  family-of-equivalences-adjoint-pair-Large-Category : UUω
  family-of-equivalences-adjoint-pair-Large-Category =
    family-of-equivalences-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  naturality-family-of-equivalences-adjoint-pair-Large-Category :
    family-of-equivalences-adjoint-pair-Large-Category → UUω
  naturality-family-of-equivalences-adjoint-pair-Large-Category =
    naturality-family-of-equivalences-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  is-adjoint-pair-Large-Category : UUω
  is-adjoint-pair-Large-Category =
    is-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  equiv-is-adjoint-pair-Large-Category :
    is-adjoint-pair-Large-Category →
    family-of-equivalences-adjoint-pair-Large-Category
  equiv-is-adjoint-pair-Large-Category =
    equiv-is-adjoint-pair-Large-Precategory

  naturality-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) →
    naturality-family-of-equivalences-adjoint-pair-Large-Category
      ( equiv-is-adjoint-pair-Large-Precategory H)
  naturality-equiv-is-adjoint-pair-Large-Category =
    naturality-equiv-is-adjoint-pair-Large-Precategory

  map-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category D (obj-functor-Large-Category C D F X) Y →
    hom-Large-Category C X (obj-functor-Large-Category D C G Y)
  map-equiv-is-adjoint-pair-Large-Category =
    map-equiv-is-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  inv-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category C X (obj-functor-Large-Category D C G Y) ≃
    hom-Large-Category D (obj-functor-Large-Category C D F X) Y
  inv-equiv-is-adjoint-pair-Large-Category =
    inv-equiv-is-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  map-inv-equiv-is-adjoint-pair-Large-Category :
    (H : is-adjoint-pair-Large-Category) {l1 l2 : Level}
    (X : obj-Large-Category C l1) (Y : obj-Large-Category D l2) →
    hom-Large-Category C X (obj-functor-Large-Category D C G Y) →
    hom-Large-Category D (obj-functor-Large-Category C D F X) Y
  map-inv-equiv-is-adjoint-pair-Large-Category =
    map-inv-equiv-is-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

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
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C (hom-functor-Large-Category D C G g) h)
          ( f))
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-functor-Large-Category C D F f))
      ( map-inv-equiv-is-adjoint-pair-Large-Category H X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Large-Category =
    naturality-inv-equiv-is-adjoint-pair-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)
```

### The predicate of being a left adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (G : functor-Large-Category γG D C)
  (F : functor-Large-Category γF C D)
  where

  is-left-adjoint-functor-Large-Category : UUω
  is-left-adjoint-functor-Large-Category =
    is-adjoint-pair-Large-Category C D F G
```

### The predicate of being a right adjoint

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG D C)
  where

  is-right-adjoint-functor-Large-Category : UUω
  is-right-adjoint-functor-Large-Category =
    is-adjoint-pair-Large-Category C D F G
```

### Adjunctions of large precategories

```agda
module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  (γ δ : Level → Level)
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  where

  Adjunction-Large-Category : UUω
  Adjunction-Large-Category =
    Adjunction-Large-Precategory γ δ
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)

module _
  {αC αD : Level → Level}
  {βC βD : Level → Level → Level}
  {γ δ : Level → Level}
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  (F : Adjunction-Large-Category γ δ C D)
  where

  left-adjoint-Adjunction-Large-Category :
    functor-Large-Category γ C D
  left-adjoint-Adjunction-Large-Category =
    left-adjoint-Adjunction-Large-Precategory F

  right-adjoint-Adjunction-Large-Category :
    functor-Large-Category δ D C
  right-adjoint-Adjunction-Large-Category =
    right-adjoint-Adjunction-Large-Precategory F

  is-adjoint-pair-Adjunction-Large-Category :
    is-adjoint-pair-Large-Category C D
      ( left-adjoint-Adjunction-Large-Category)
      ( right-adjoint-Adjunction-Large-Category)
  is-adjoint-pair-Adjunction-Large-Category =
    is-adjoint-pair-Adjunction-Large-Precategory F

  obj-left-adjoint-Adjunction-Large-Category :
    {l : Level} → obj-Large-Category C l → obj-Large-Category D (γ l)
  obj-left-adjoint-Adjunction-Large-Category =
    obj-left-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  hom-left-adjoint-Adjunction-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category C l1}
    {Y : obj-Large-Category C l2} →
    hom-Large-Category C X Y →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category X)
      ( obj-left-adjoint-Adjunction-Large-Category Y)
  hom-left-adjoint-Adjunction-Large-Category =
    hom-left-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-id-left-adjoint-Adjunction-Large-Category :
    {l1 : Level}
    (X : obj-Large-Category C l1) →
    hom-left-adjoint-Adjunction-Large-Category
      ( id-hom-Large-Category C {X = X}) ＝
    id-hom-Large-Category D
  preserves-id-left-adjoint-Adjunction-Large-Category =
    preserves-id-left-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  obj-right-adjoint-Adjunction-Large-Category :
    {l1 : Level} → obj-Large-Category D l1 → obj-Large-Category C (δ l1)
  obj-right-adjoint-Adjunction-Large-Category =
    obj-right-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  hom-right-adjoint-Adjunction-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category D l1}
    {Y : obj-Large-Category D l2} →
    hom-Large-Category D X Y →
    hom-Large-Category C
      ( obj-right-adjoint-Adjunction-Large-Category X)
      ( obj-right-adjoint-Adjunction-Large-Category Y)
  hom-right-adjoint-Adjunction-Large-Category =
    hom-right-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-id-right-adjoint-Adjunction-Large-Category :
    {l : Level}
    (Y : obj-Large-Category D l) →
    hom-right-adjoint-Adjunction-Large-Category
      ( id-hom-Large-Category D {X = Y}) ＝
    id-hom-Large-Category C
  preserves-id-right-adjoint-Adjunction-Large-Category =
    preserves-id-right-adjoint-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  equiv-is-adjoint-pair-Adjunction-Large-Category :
    family-of-equivalences-adjoint-pair-Large-Category C D
      ( left-adjoint-Adjunction-Large-Category)
      ( right-adjoint-Adjunction-Large-Category)
  equiv-is-adjoint-pair-Adjunction-Large-Category =
    equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  map-equiv-is-adjoint-pair-Adjunction-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category X)
      ( Y) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category Y)
  map-equiv-is-adjoint-pair-Adjunction-Large-Category =
    map-equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Category :
    naturality-family-of-equivalences-adjoint-pair-Large-Category C D
      ( left-adjoint-Adjunction-Large-Category)
      ( right-adjoint-Adjunction-Large-Category)
      ( equiv-is-adjoint-pair-Adjunction-Large-Category)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Category =
    naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category Y) ≃
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category X)
      ( Y)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Category =
    inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category C l1)
    (Y : obj-Large-Category D l2) →
    hom-Large-Category C
      ( X)
      ( obj-right-adjoint-Adjunction-Large-Category Y) →
    hom-Large-Category D
      ( obj-left-adjoint-Adjunction-Large-Category X)
      ( Y)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category :
    {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Category C l1}
    {X2 : obj-Large-Category C l2}
    {Y1 : obj-Large-Category D l3}
    {Y2 : obj-Large-Category D l4}
    (f : hom-Large-Category C X2 X1)
    (g : hom-Large-Category D Y1 Y2) →
    coherence-square-maps
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category X1 Y1)
      ( λ h →
        comp-hom-Large-Category C
          ( comp-hom-Large-Category C
            ( hom-right-adjoint-Adjunction-Large-Category g)
            ( h))
          ( f))
      ( λ h →
        comp-hom-Large-Category D
          ( comp-hom-Large-Category D g h)
          ( hom-left-adjoint-Adjunction-Large-Category f))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Category X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Category =
    naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
```

### The unit of an adjunction

Given an adjoint pair `F ⊣ G`, we construct a natural transformation
`η : id → G ∘ F` called the **unit** of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} {γ δ : Level → Level}
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  (F : Adjunction-Large-Category γ δ C D)
  where

  hom-unit-Adjunction-Large-Category :
    family-of-morphisms-functor-Large-Category C C
      ( id-functor-Large-Category C)
      ( comp-functor-Large-Category C D C
        ( right-adjoint-Adjunction-Large-Category C D F)
        ( left-adjoint-Adjunction-Large-Category C D F))
  hom-unit-Adjunction-Large-Category =
    hom-unit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  naturality-unit-Adjunction-Large-Category :
    naturality-family-of-morphisms-functor-Large-Category C C
      ( id-functor-Large-Category C)
      ( comp-functor-Large-Category C D C
        ( right-adjoint-Adjunction-Large-Category C D F)
        ( left-adjoint-Adjunction-Large-Category C D F))
      ( hom-unit-Adjunction-Large-Category)
  naturality-unit-Adjunction-Large-Category =
    naturality-unit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  unit-Adjunction-Large-Category :
    natural-transformation-Large-Category C C
      ( id-functor-Large-Category C)
      ( comp-functor-Large-Category C D C
        ( right-adjoint-Adjunction-Large-Category C D F)
        ( left-adjoint-Adjunction-Large-Category C D F))
  unit-Adjunction-Large-Category =
    unit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
```

### The counit of an adjunction

Given an adjoint pair `F ⊣ G`, we construct a natural transformation
`ε : F ∘ G → id` called the **counit** of the adjunction.

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} {γ δ : Level → Level}
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  (F : Adjunction-Large-Category γ δ C D)
  where

  hom-counit-Adjunction-Large-Category :
    family-of-morphisms-functor-Large-Category D D
      ( comp-functor-Large-Category D C D
        ( left-adjoint-Adjunction-Large-Category C D F)
        ( right-adjoint-Adjunction-Large-Category C D F))
      ( id-functor-Large-Category D)
  hom-counit-Adjunction-Large-Category =
    hom-counit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  naturality-counit-Adjunction-Large-Category :
    naturality-family-of-morphisms-functor-Large-Category D D
      ( comp-functor-Large-Category D C D
        ( left-adjoint-Adjunction-Large-Category C D F)
        ( right-adjoint-Adjunction-Large-Category C D F))
      ( id-functor-Large-Category D)
      ( hom-counit-Adjunction-Large-Category)
  naturality-counit-Adjunction-Large-Category =
    naturality-counit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  counit-Adjunction-Large-Category :
    natural-transformation-Large-Category D D
      ( comp-functor-Large-Category D C D
        ( left-adjoint-Adjunction-Large-Category C D F)
        ( right-adjoint-Adjunction-Large-Category C D F))
      ( id-functor-Large-Category D)
  counit-Adjunction-Large-Category =
    counit-Adjunction-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
```
