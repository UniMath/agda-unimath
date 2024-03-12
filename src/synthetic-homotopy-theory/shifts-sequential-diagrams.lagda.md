# Shifts of sequential diagrams

```agda
module synthetic-homotopy-theory.shifts-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-identifications
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A
{{#concept "shift" Disambiguation="sequential diagram" Agda=shift-sequential-diagram}}
of a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md) is a
sequential diagram consisting of the types and maps shifted by one. It is also
denoted `A[1]`.

Similarly, a
{{#concept "shift" Disambiguation="morphism of sequential diagrams" Agda=shift-hom-sequential-diagram}}
of a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
is a morphism from the shifted domain into the shifted codomain.

Importantly, the sequential colimit of a shifted sequential diagram is
equivalent to the colimit of the original diagram.

## Definitions

### Shifts of sequential diagrams

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  shift-sequential-diagram : sequential-diagram l1
  pr1 shift-sequential-diagram n = family-sequential-diagram A (succ-ℕ n)
  pr2 shift-sequential-diagram n = map-sequential-diagram A (succ-ℕ n)
```

### Shifts of morphisms of sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  (f : hom-sequential-diagram A B)
  where

  shift-hom-sequential-diagram :
    hom-sequential-diagram
      ( shift-sequential-diagram A)
      ( shift-sequential-diagram B)
  pr1 shift-hom-sequential-diagram n =
    map-hom-sequential-diagram B f (succ-ℕ n)
  pr2 shift-hom-sequential-diagram n =
    naturality-map-hom-sequential-diagram B f (succ-ℕ n)
```

## Properties

### Sequential diagrams map into their shifts

The morphism is obtained by observing that the squares in the diagram

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    v       v       v
    A₁ ---> A₂ ---> A₃ ---> ⋯
        a₁      a₂
```

commute by reflexivity.

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  hom-shift-sequential-diagram :
    hom-sequential-diagram
      ( A)
      ( shift-sequential-diagram A)
  pr1 hom-shift-sequential-diagram = map-sequential-diagram A
  pr2 hom-shift-sequential-diagram n = refl-htpy
```

### The type of cocones under a sequential diagram is equivalent to the type of cocones under its shift

Given a cocone

```text
      a₀      a₁
  A₀ ---> A₁ ---> A₂ ---> ⋯
   \      |      /
    \     |     /
  i₀ \    | i₁ / i₂
      \   |   /
       V  V  V
          X
```

under `A`, we may forget the first injection and homotopy to get the cocone

```text
              a₁
          A₁ ---> A₂ ---> ⋯
          |      /
          |     /
          | i₁ / i₂
          |   /
          V  V
          X
```

under `A[1]`.

Conversely, given a cocone

```text
        a₁      a₁
    A₁ ---> A₂ ---> A₃ ---> ⋯
     \      |      /
      \     |     /
    i₁ \    | i₂ / i₃
        \   |   /
         V  V  V
            X
```

under `A[1]`, we may precompose it with the morphism `A → A[1]` to get the
cocone

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    v       v       v
    A₁ ---> A₂ ---> A₃ ---> ⋯
     \  a₁  |   a₁  /
      \     |     /
    i₁ \    | i₂ / i₃
        \   |   /
         V  V  V
            X
```

under `A`.

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1)
  {X : UU l2}
  where

  cocone-shift-sequential-diagram :
    cocone-sequential-diagram A X →
    cocone-sequential-diagram (shift-sequential-diagram A) X
  pr1 (cocone-shift-sequential-diagram c) n =
    map-cocone-sequential-diagram c (succ-ℕ n)
  pr2 (cocone-shift-sequential-diagram c) n =
    coherence-cocone-sequential-diagram c (succ-ℕ n)

  cocone-unshift-sequential-diagram :
    cocone-sequential-diagram (shift-sequential-diagram A) X →
    cocone-sequential-diagram A X
  cocone-unshift-sequential-diagram c =
    map-cocone-hom-sequential-diagram
      ( hom-shift-sequential-diagram A)
      ( c)

module _
  {l1 l2 : Level} (A : sequential-diagram l1)
  (X : UU l2)
  where

  -- TODO: Why are these two proofs so similar? Could it be abstracted?
  -- The diff is whiskering with the map of A or A[1]
  -- htpy-is-section-cocone-unshift-sequential-diagram :
  --   (c : cocone-sequential-diagram (shift-sequential-diagram A) X) →
  --   htpy-cocone-sequential-diagram
  --     ( cocone-shift-sequential-diagram A
  --       ( cocone-unshift-sequential-diagram A c))
  --     ( c)
  -- pr1 (htpy-is-section-cocone-unshift-sequential-diagram c) n =
  --   inv-htpy (coherence-cocone-sequential-diagram c n)
  -- pr2 (htpy-is-section-cocone-unshift-sequential-diagram c) n =
  --   ( ap-concat-htpy'
  --     ( inv-htpy
  --       ( ( coherence-cocone-sequential-diagram c (succ-ℕ n))) ·r
  --         ( map-sequential-diagram (shift-sequential-diagram A) n))
  --     ( right-unit-htpy)) ∙h
  --   ( right-inv-htpy
  --     ( ( coherence-cocone-sequential-diagram c (succ-ℕ n)) ·r
  --       ( map-sequential-diagram (shift-sequential-diagram A) n))) ∙h
  --   ( inv-htpy-left-inv-htpy (coherence-cocone-sequential-diagram c n))

  htpy-is-section-cocone-unshift-sequential-diagram' :
    (c : cocone-sequential-diagram (shift-sequential-diagram A) X) →
    htpy-cocone-sequential-diagram
      ( c)
      ( cocone-shift-sequential-diagram A
        ( cocone-unshift-sequential-diagram A c))
  pr1 (htpy-is-section-cocone-unshift-sequential-diagram' c) =
    coherence-cocone-sequential-diagram c
  pr2 (htpy-is-section-cocone-unshift-sequential-diagram' c) n =
    left-whisker-concat-htpy
      ( coherence-cocone-sequential-diagram c n)
      ( inv-htpy-right-unit-htpy)

  is-section-cocone-unshift-sequential-diagram :
    is-section
      ( cocone-shift-sequential-diagram A {X})
      ( cocone-unshift-sequential-diagram A {X})
  is-section-cocone-unshift-sequential-diagram c =
    inv
      ( eq-htpy-cocone-sequential-diagram
        ( shift-sequential-diagram A)
        ( _)
        ( _)
        ( htpy-is-section-cocone-unshift-sequential-diagram' c))

  -- htpy-is-retraction-cocone-unshift-sequential-diagram :
  --   (c : cocone-sequential-diagram A X) →
  --   htpy-cocone-sequential-diagram
  --     ( cocone-unshift-sequential-diagram A
  --       ( cocone-shift-sequential-diagram A c))
  --     ( c)
  -- pr1 (htpy-is-retraction-cocone-unshift-sequential-diagram c) n =
  --   inv-htpy (coherence-cocone-sequential-diagram c n)
  -- pr2 (htpy-is-retraction-cocone-unshift-sequential-diagram c) n =
  --   ( ap-concat-htpy'
  --     ( inv-htpy
  --       ( ( coherence-cocone-sequential-diagram c (succ-ℕ n))) ·r
  --         ( map-sequential-diagram A n))
  --     ( right-unit-htpy)) ∙h
  --   ( right-inv-htpy
  --     ( ( coherence-cocone-sequential-diagram c (succ-ℕ n)) ·r
  --       ( map-sequential-diagram A n))) ∙h
  --   ( inv-htpy-left-inv-htpy (coherence-cocone-sequential-diagram c n))

  htpy-is-retraction-cocone-unshift-sequential-diagram' :
    (c : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram
      ( c)
      ( cocone-unshift-sequential-diagram A
        ( cocone-shift-sequential-diagram A c))
  pr1 (htpy-is-retraction-cocone-unshift-sequential-diagram' c) =
    coherence-cocone-sequential-diagram c
  pr2 (htpy-is-retraction-cocone-unshift-sequential-diagram' c) n =
    left-whisker-concat-htpy
      ( coherence-cocone-sequential-diagram c n)
      ( inv-htpy-right-unit-htpy)

  is-retraction-cocone-unshift-sequential-diagram :
    is-retraction
      ( cocone-shift-sequential-diagram A {X})
      ( cocone-unshift-sequential-diagram A {X})
  is-retraction-cocone-unshift-sequential-diagram c =
    inv
      ( eq-htpy-cocone-sequential-diagram A _ _
        ( htpy-is-retraction-cocone-unshift-sequential-diagram' c))

  is-equiv-cocone-shift-sequential-diagram :
    is-equiv (cocone-shift-sequential-diagram A {X})
  is-equiv-cocone-shift-sequential-diagram =
    is-equiv-is-invertible
      ( cocone-unshift-sequential-diagram A {X})
      ( is-section-cocone-unshift-sequential-diagram)
      ( is-retraction-cocone-unshift-sequential-diagram)

  equiv-cocone-shift-unshift-sequential-diagram :
    cocone-sequential-diagram A X ≃
    cocone-sequential-diagram (shift-sequential-diagram A) X
  pr1 equiv-cocone-shift-unshift-sequential-diagram =
    cocone-shift-sequential-diagram A {X}
  pr2 equiv-cocone-shift-unshift-sequential-diagram =
    is-equiv-cocone-shift-sequential-diagram
```

### The sequential colimit of a sequential diagram is also the sequential colimit of the shifted diagram

Given a sequential colimit

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X,
```

there is a commuting triangle

```text
              cocone-map
      X → Y ------------> cocone A Y
            \           /
  cocone-map  \       / ≃
                V   V
             cocone A[1] Y,
```

where the top map is an equivalence by the universal property of `X`, and the
right map was shown to be an equivalence above. It follows that the third map is
also an equivalence, which makes `X` the sequential colimit of `A[1]`.

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1)
  {X : UU l2} {c : cocone-sequential-diagram A X}
  where

  triangle-cocone-map-blabla :
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram
        ( cocone-shift-sequential-diagram A c)
        { Y = Y})
      ( cocone-shift-sequential-diagram A)
      ( cocone-map-sequential-diagram c)
  triangle-cocone-map-blabla Y = refl-htpy

  up-cocone-shift-sequential-diagram :
    universal-property-sequential-colimit c →
    universal-property-sequential-colimit (cocone-shift-sequential-diagram A c)
  up-cocone-shift-sequential-diagram up-c Y =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram
        ( cocone-shift-sequential-diagram A c)
        { Y = Y})
      ( cocone-shift-sequential-diagram A)
      ( cocone-map-sequential-diagram c)
      ( triangle-cocone-map-blabla Y)
      ( up-c Y)
      ( is-equiv-cocone-shift-sequential-diagram A Y)
```

