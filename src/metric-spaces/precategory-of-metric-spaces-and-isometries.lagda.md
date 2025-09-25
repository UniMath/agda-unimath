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
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definitions

```agda
module _
  {l1 l2 : Level}
  where

  precategory-isometry-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  precategory-isometry-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( set-isometry-Metric-Space)
      ( λ {A B C} → comp-isometry-Metric-Space A B C)
      ( isometry-id-Metric-Space)
      ( λ {A B C D} → associative-comp-isometry-Metric-Space A B C D)
      ( λ {A B} → left-unit-law-comp-isometry-Metric-Space A B)
      ( λ {A B} → right-unit-law-comp-isometry-Metric-Space A B)
```

## Properties

### Isomorphisms in the precategory of metric spaces and isometries are equivalences

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : isometry-Metric-Space A B)
  where

  is-equiv-is-iso-isometry-Metric-Space :
    is-iso-Precategory precategory-isometry-Metric-Space {A} {B} f →
    is-equiv (map-isometry-Metric-Space A B f)
  is-equiv-is-iso-isometry-Metric-Space (g , H) =
    is-equiv-is-invertible
      ( map-isometry-Metric-Space B A g)
      ( htpy-eq (ap (map-isometry-Metric-Space B B) (pr1 H)))
      ( htpy-eq (ap (map-isometry-Metric-Space A A) (pr2 H)))
```

### Isometric equivalences are isomorphisms in the precategory of metric spaces and isometries

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : isometry-Metric-Space A B)
  (E : is-equiv (map-isometry-Metric-Space A B f))
  where

  is-iso-is-equiv-isometry-Metric-Space :
    is-iso-Precategory precategory-isometry-Metric-Space {A} {B} f
  pr1 is-iso-is-equiv-isometry-Metric-Space =
    isometry-inv-is-equiv-isometry-Metric-Space A B f E
  pr2 is-iso-is-equiv-isometry-Metric-Space =
    ( is-section-isometry-inv-is-equiv-isometry-Metric-Space A B f E) ,
    ( is-retraction-isometry-inv-is-equiv-isometry-Metric-Space A B f E)
```

### Isomorphic types in the precategory of metric spaces are isometrically equivalent

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-iso-isometric-equiv-Metric-Space' :
    iso-Precategory precategory-isometry-Metric-Space A B ≃
    isometric-equiv-Metric-Space' A B
  equiv-iso-isometric-equiv-Metric-Space' =
    ( equiv-tot (λ f → commutative-product)) ∘e
    ( associative-Σ) ∘e
    ( equiv-tot
      ( λ f →
        equiv-iff
          ( is-iso-prop-Precategory
            ( precategory-isometry-Metric-Space)
            { A}
            { B}
            ( f))
          ( is-equiv-Prop
            ( map-isometry-Metric-Space A B f))
          ( is-equiv-is-iso-isometry-Metric-Space A B f)
          ( is-iso-is-equiv-isometry-Metric-Space A B f)))
```

## See also

- The
  [category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md).
