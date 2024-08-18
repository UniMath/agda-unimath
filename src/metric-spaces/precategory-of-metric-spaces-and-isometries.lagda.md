# The precategory of metric spaces and isometries

```agda
module metric-spaces.precategory-of-metric-spaces-and-isometries where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [isometries](metric-spaces.isometry-metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-isometry-Metric-Space : Precategory (lsuc l) l
  precategory-isometry-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-isometry-function-Metric-Space)
      ( λ {A B C} → comp-isometry-function-Metric-Space A B C)
      ( isometry-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-isometry-function-Metric-Space
          ( A)
          ( D)
          ( comp-isometry-function-Metric-Space A B D
            ( comp-isometry-function-Metric-Space B C D h g)
            ( f))
          ( comp-isometry-function-Metric-Space A C D
            ( h)
            ( comp-isometry-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-isometry-function-Metric-Space A B
          ( comp-isometry-function-Metric-Space A B B
            ( isometry-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-isometry-function-Metric-Space A B
          ( comp-isometry-function-Metric-Space A A B
            ( f)
            ( isometry-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```

## Properties

### Isomorphic types in the precategory of metric spaces and isometries are equal

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  eq-iso-precategory-isometry-Metric-Space :
    iso-Precategory precategory-isometry-Metric-Space A B → A ＝ B
  eq-iso-precategory-isometry-Metric-Space f =
    eq-isometric-is-equiv-Metric-Space
      ( A)
      ( B)
      ( map-isometry-function-Metric-Space
        ( A)
        ( B)
        ( hom-iso-Precategory precategory-isometry-Metric-Space {A} {B} f))
      ( rec-Σ
        ( λ g H →
          ( map-isometry-function-Metric-Space B A g ,
            htpy-eq (ap (map-isometry-function-Metric-Space B B) (pr1 H))) ,
          ( map-isometry-function-Metric-Space B A g ,
            htpy-eq (ap (map-isometry-function-Metric-Space A A) (pr2 H))))
        ( is-iso-iso-Precategory precategory-isometry-Metric-Space {A} {B} f))
      ( is-isometry-map-isometry-function-Metric-Space
        ( A)
        ( B)
        ( hom-iso-Precategory precategory-isometry-Metric-Space {A} {B} f))
```
