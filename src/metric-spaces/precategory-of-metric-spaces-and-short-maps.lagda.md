# The precategory of metric spaces and short maps

```agda
module metric-spaces.precategory-of-metric-spaces-and-short-maps where
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
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

The [short maps](metric-spaces.short-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  precategory-short-map-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  precategory-short-map-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( set-short-map-Metric-Space)
      ( λ {A B C} → comp-short-map-Metric-Space A B C)
      ( id-short-map-Metric-Space)
      ( λ {A B C D} → associative-comp-short-map-Metric-Space A B C D)
      ( λ {A B} → left-unit-law-comp-short-map-Metric-Space A B)
      ( λ {A B} → right-unit-law-comp-short-map-Metric-Space A B)
```

## Properties

### Isomorphisms in the precategory of metric spaces and short maps are equivalences

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-map-Metric-Space A B)
  where

  is-equiv-is-iso-short-map-Metric-Space :
    is-iso-Precategory precategory-short-map-Metric-Space {A} {B} f →
    is-equiv (map-short-map-Metric-Space A B f)
  is-equiv-is-iso-short-map-Metric-Space (g , I , J) =
    is-equiv-is-invertible
      ( map-short-map-Metric-Space B A g)
      ( htpy-eq (ap (map-short-map-Metric-Space B B) I))
      ( htpy-eq (ap (map-short-map-Metric-Space A A) J))
```

### Isomorphisms in the precategory of metric spaces and short maps are isometries

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-map-Metric-Space A B)
  where

  abstract
    is-isometry-is-iso-short-map-Metric-Space :
      is-iso-Precategory precategory-short-map-Metric-Space {A} {B} f →
      is-isometry-Metric-Space A B (map-short-map-Metric-Space A B f)
    pr1 (is-isometry-is-iso-short-map-Metric-Space I d x y) =
      is-short-map-short-map-Metric-Space A B f d x y
    pr2 (is-isometry-is-iso-short-map-Metric-Space I d x y) H =
      binary-tr
        ( neighborhood-Metric-Space A d)
          ( ap
            ( λ K → map-short-map-Metric-Space A A K x)
            ( is-retraction-hom-inv-is-iso-Precategory
              precategory-short-map-Metric-Space
              { A}
              { B}
              ( I)))
          ( ap
            ( λ K → map-short-map-Metric-Space A A K y)
            ( is-retraction-hom-inv-is-iso-Precategory
              precategory-short-map-Metric-Space
              { A}
              { B}
              ( I)))
          ( is-short-map-short-map-Metric-Space
            ( B)
            ( A)
            ( hom-inv-is-iso-Precategory
              ( precategory-short-map-Metric-Space)
              { A}
              { B}
              ( I))
            ( d)
            ( map-short-map-Metric-Space A B f x)
            ( map-short-map-Metric-Space A B f y)
            ( H))
```

### A short map between metric spaces is an isomorphism if and only if its carrier map is an isometric equivalence

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : short-map-Metric-Space A B)
  where

  is-iso-is-isometric-equiv-short-map-Metric-Space :
    ( is-equiv (map-short-map-Metric-Space A B f) ×
      is-isometry-Metric-Space A B (map-short-map-Metric-Space A B f)) →
    is-iso-Precategory precategory-short-map-Metric-Space {A} {B} f
  is-iso-is-isometric-equiv-short-map-Metric-Space (E , I) =
    ( short-map-inverse) ,
    ( ( eq-htpy-map-short-map-Metric-Space
      ( B)
      ( B)
      ( comp-short-map-Metric-Space
        ( B)
        ( A)
        ( B)
        ( f)
        ( short-map-inverse))
      ( id-short-map-Metric-Space B)
      ( is-section-map-inv-is-equiv E)) ,
      ( eq-htpy-map-short-map-Metric-Space
        ( A)
        ( A)
        ( comp-short-map-Metric-Space
          ( A)
          ( B)
          ( A)
          ( short-map-inverse)
          ( f))
        ( id-short-map-Metric-Space A)
        ( is-retraction-map-inv-is-equiv E)))
      where

      short-map-inverse : short-map-Metric-Space B A
      short-map-inverse =
        short-map-isometry-Metric-Space
          ( B)
          ( A)
          ( isometry-inv-is-equiv-isometry-Metric-Space
            ( A)
            ( B)
            ( map-short-map-Metric-Space A B f , I)
            ( E))
```

### A map between metric spaces is a short isomorphism if and only if it is an isometric equivalence

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  (f : map-Metric-Space A B)
  where

  equiv-is-isometric-equiv-is-iso-short-map-Metric-Space :
    Σ ( is-short-map-Metric-Space A B f)
      ( λ s →
        is-iso-Precategory precategory-short-map-Metric-Space
          { A}
          { B}
          ( f , s)) ≃
    (is-equiv f) × (is-isometry-Metric-Space A B f)
  equiv-is-isometric-equiv-is-iso-short-map-Metric-Space =
    equiv-iff
      ( Σ-Prop
        ( is-short-map-prop-Metric-Space A B f)
        ( λ s →
          is-iso-prop-Precategory precategory-short-map-Metric-Space
            { A}
            { B}
            ( f , s)))
      ( product-Prop
        ( is-equiv-Prop f)
        ( is-isometry-prop-Metric-Space A B f))
    ( λ (is-short-f , is-iso-f) →
      is-equiv-is-iso-short-map-Metric-Space
        ( A)
        ( B)
        ( f , is-short-f)
        ( is-iso-f) ,
      is-isometry-is-iso-short-map-Metric-Space
        ( A)
        ( B)
        ( f , is-short-f)
        ( is-iso-f))
    ( λ (is-equiv-f , is-isometry-f) →
      is-short-map-is-isometry-Metric-Space A B f is-isometry-f ,
      is-iso-is-isometric-equiv-short-map-Metric-Space
        ( A)
        ( B)
        ( f , is-short-map-is-isometry-Metric-Space A B f is-isometry-f)
        ( is-equiv-f , is-isometry-f))
```

### Two metric spaces are isomorphic in the precategory of metric spaces and short maps if and only if there is an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-isometric-equiv-iso-short-map-Metric-Space' :
    iso-Precategory precategory-short-map-Metric-Space A B ≃
    isometric-equiv-Metric-Space' A B
  equiv-isometric-equiv-iso-short-map-Metric-Space' =
    ( equiv-tot
      ( equiv-is-isometric-equiv-is-iso-short-map-Metric-Space A B)) ∘e
    ( associative-Σ)

  map-equiv-isometric-equiv-iso-short-map-Metric-Space' :
    iso-Precategory precategory-short-map-Metric-Space A B →
    isometric-equiv-Metric-Space' A B
  map-equiv-isometric-equiv-iso-short-map-Metric-Space' =
    map-equiv
      ( equiv-isometric-equiv-iso-short-map-Metric-Space')
```

## See also

- The
  [category of metric spaces and short maps](metric-spaces.category-of-metric-spaces-and-short-maps.md).
