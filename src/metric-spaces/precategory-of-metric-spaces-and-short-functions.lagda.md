# The precategory of metric spaces and short functions

```agda
module metric-spaces.precategory-of-metric-spaces-and-short-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The [short functions](metric-spaces.short-functions-metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-short-function-Metric-Space : Precategory (lsuc l) l
  precategory-short-function-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-short-function-Metric-Space)
      ( λ {A B C} → comp-short-function-Metric-Space A B C)
      ( short-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-short-function-Metric-Space
          ( A)
          ( D)
          ( comp-short-function-Metric-Space A B D
            ( comp-short-function-Metric-Space B C D h g)
            ( f))
          ( comp-short-function-Metric-Space A C D
            ( h)
            ( comp-short-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-short-function-Metric-Space A B
          ( comp-short-function-Metric-Space A B B
            ( short-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-short-function-Metric-Space A B
          ( comp-short-function-Metric-Space A A B
            ( f)
            ( short-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```

## Properties

### Isomorphisms in the precategory of metric spaces and short maps are isometries

```agda
module _
  {l : Level} (A B : Metric-Space l) (f : short-function-Metric-Space A B)
  (I : is-iso-Precategory precategory-short-function-Metric-Space {A} {B} f)
  where

  is-isometry-is-iso-precategory-short-function-Metric-Space :
    is-isometry-function-Metric-Space A B
      (map-short-function-Metric-Space A B f)
  is-isometry-is-iso-precategory-short-function-Metric-Space d x y =
    ( is-short-map-short-function-Metric-Space A B f d x y) ,
    ( λ H →
      binary-tr
        ( is-in-neighbourhood-Metric-Space A d)
        ( ap
          (λ K → map-short-function-Metric-Space A A K x)
          ( is-retraction-hom-inv-is-iso-Precategory
            precategory-short-function-Metric-Space
            { A}
            { B}
            ( I)))
        ( ap
          (λ K → map-short-function-Metric-Space A A K y)
          ( is-retraction-hom-inv-is-iso-Precategory
            precategory-short-function-Metric-Space
            { A}
            { B}
            ( I)))
        ( is-short-map-short-function-Metric-Space
          ( B)
          ( A)
          ( hom-inv-is-iso-Precategory
            ( precategory-short-function-Metric-Space)
            { A}
            { B}
            ( I))
          ( d)
          ( map-short-function-Metric-Space A B f x)
          ( map-short-function-Metric-Space A B f y)
          ( H)))
```
