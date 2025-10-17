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
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The [short functions](metric-spaces.short-functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  precategory-short-function-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  precategory-short-function-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( set-short-function-Metric-Space)
      ( λ {A B C} → comp-short-function-Metric-Space A B C)
      ( short-id-Metric-Space)
      ( λ {A B C D} → associative-comp-short-function-Metric-Space A B C D)
      ( λ {A B} → left-unit-law-comp-short-function-Metric-Space A B)
      ( λ {A B} → right-unit-law-comp-short-function-Metric-Space A B)
```

## Properties

### Isomorphisms in the precategory of metric spaces and short maps are equivalences

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-function-Metric-Space A B)
  where

  is-equiv-is-iso-short-function-Metric-Space :
    is-iso-Precategory precategory-short-function-Metric-Space {A} {B} f →
    is-equiv (map-short-function-Metric-Space A B f)
  is-equiv-is-iso-short-function-Metric-Space (g , I , J) =
    is-equiv-is-invertible
      ( map-short-function-Metric-Space B A g)
      ( htpy-eq (ap (map-short-function-Metric-Space B B) I))
      ( htpy-eq (ap (map-short-function-Metric-Space A A) J))
```

### Isomorphisms in the precategory of metric spaces and short maps are isometries

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-function-Metric-Space A B)
  where

  is-isometry-is-iso-short-function-Metric-Space :
    is-iso-Precategory precategory-short-function-Metric-Space {A} {B} f →
    is-isometry-Metric-Space A B (map-short-function-Metric-Space A B f)
  pr1 (is-isometry-is-iso-short-function-Metric-Space I d x y) =
    is-short-map-short-function-Metric-Space A B f d x y
  pr2 (is-isometry-is-iso-short-function-Metric-Space I d x y) H =
    binary-tr
      ( neighborhood-Metric-Space A d)
        ( ap
          ( λ K → map-short-function-Metric-Space A A K x)
          ( is-retraction-hom-inv-is-iso-Precategory
            precategory-short-function-Metric-Space
            { A}
            { B}
            ( I)))
        ( ap
          ( λ K → map-short-function-Metric-Space A A K y)
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
          ( H))
```

### A short map between metric spaces is an isomorphism if and only if its carrier map is an isometric equivalence

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-function-Metric-Space A B)
  where

  is-iso-is-isometric-equiv-short-function-Metric-Space :
    ( is-equiv (map-short-function-Metric-Space A B f) ×
      is-isometry-Metric-Space A B (map-short-function-Metric-Space A B f)) →
    is-iso-Precategory precategory-short-function-Metric-Space {A} {B} f
  is-iso-is-isometric-equiv-short-function-Metric-Space (E , I) =
    ( short-inverse) ,
    ( ( eq-htpy-map-short-function-Metric-Space
      ( B)
      ( B)
      ( comp-short-function-Metric-Space
        ( B)
        ( A)
        ( B)
        ( f)
        ( short-inverse))
      ( short-id-Metric-Space B)
      ( is-section-map-inv-is-equiv E)) ,
      ( eq-htpy-map-short-function-Metric-Space
        ( A)
        ( A)
        ( comp-short-function-Metric-Space
          ( A)
          ( B)
          ( A)
          ( short-inverse)
          ( f))
        ( short-id-Metric-Space A)
        ( is-retraction-map-inv-is-equiv E)))
      where

      short-inverse : short-function-Metric-Space B A
      short-inverse =
        short-isometry-Metric-Space
          ( B)
          ( A)
          ( isometry-inv-is-equiv-isometry-Metric-Space
            ( A)
            ( B)
            ( map-short-function-Metric-Space A B f , I)
            ( E))
```

### A function between metric spaces is a short isomorphism if and only if it an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  (f : type-function-Metric-Space A B)
  where

  equiv-is-isometric-equiv-is-iso-short-function-Metric-Space :
    Σ ( is-short-function-Metric-Space A B f)
      ( λ s →
        is-iso-Precategory precategory-short-function-Metric-Space
          { A}
          { B}
          ( f , s)) ≃
    (is-equiv f) × (is-isometry-Metric-Space A B f)
  equiv-is-isometric-equiv-is-iso-short-function-Metric-Space =
    equiv-iff
      ( Σ-Prop
        ( is-short-function-prop-Metric-Space A B f)
        ( λ s →
          is-iso-prop-Precategory precategory-short-function-Metric-Space
            { A}
            { B}
            ( f , s)))
      ( product-Prop
        ( is-equiv-Prop f)
        ( is-isometry-prop-Metric-Space A B f))
    ( λ (is-short-f , is-iso-f) →
      is-equiv-is-iso-short-function-Metric-Space
        ( A)
        ( B)
        ( f , is-short-f)
        ( is-iso-f) ,
      is-isometry-is-iso-short-function-Metric-Space
        ( A)
        ( B)
        ( f , is-short-f)
        ( is-iso-f))
    ( λ (is-equiv-f , is-isometry-f) →
      is-short-is-isometry-Metric-Space A B f is-isometry-f ,
      is-iso-is-isometric-equiv-short-function-Metric-Space
        ( A)
        ( B)
        ( f , is-short-is-isometry-Metric-Space A B f is-isometry-f)
        ( is-equiv-f , is-isometry-f))
```

### Two metric spaces are isomorphic in the precategory of metric spaces and short maps if and only if there is an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where
  equiv-isometric-equiv-iso-short-function-Metric-Space' :
    iso-Precategory precategory-short-function-Metric-Space A B ≃
    isometric-equiv-Metric-Space' A B
  equiv-isometric-equiv-iso-short-function-Metric-Space' =
    ( equiv-tot
      ( equiv-is-isometric-equiv-is-iso-short-function-Metric-Space A B)) ∘e
    ( associative-Σ)
```

## See also

- The
  [category of metric spaces and short functions](metric-spaces.category-of-metric-spaces-and-short-functions.md).
