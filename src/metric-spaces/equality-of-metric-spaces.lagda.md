# Equality of metric spaces

```agda
module metric-spaces.equality-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.equality-of-pseudometric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

[Equality](foundation-core.identity-types.md) of
[metric spaces](metric-spaces.metric-spaces.md) is characterized by the
following equivalent concepts:

- an equality between their carrier types such that the induced map under
  [`map-eq`](foundation-core.univalence.md) is an
  [isometry](metric-spaces.isometries-metric-spaces.md);

- an [equivalence](foundation-core.equivalences.md) between their carrier types
  such that the induced map under `map-equiv` is an isometry;

- a function between their carrier types that is both an equivalence and an
  isometry.

## Definitions

### Isometric equality of metric spaces

```agda
module _
  {l1 l2 l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1 l2')
  where

  isometric-eq-Metric-Space : UU (lsuc l1 ⊔ l2 ⊔ l2')
  isometric-eq-Metric-Space =
    isometric-eq-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

### Isometric equivalence of metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometric-equiv-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Metric-Space =
    isometric-equiv-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  equiv-isometric-equiv-Metric-Space :
    isometric-equiv-Metric-Space → type-Metric-Space A ≃ type-Metric-Space B
  equiv-isometric-equiv-Metric-Space = pr1

  map-isometric-equiv-Metric-Space :
    isometric-equiv-Metric-Space → type-Metric-Space A → type-Metric-Space B
  map-isometric-equiv-Metric-Space e =
    map-equiv (equiv-isometric-equiv-Metric-Space e)

  map-inv-isometric-equiv-Metric-Space :
    isometric-equiv-Metric-Space → type-Metric-Space B → type-Metric-Space A
  map-inv-isometric-equiv-Metric-Space e =
    map-inv-equiv (equiv-isometric-equiv-Metric-Space e)

  is-section-map-inv-isometric-equiv-Metric-Space :
    (e : isometric-equiv-Metric-Space) →
    is-section
      ( map-isometric-equiv-Metric-Space e)
      ( map-inv-isometric-equiv-Metric-Space e)
  is-section-map-inv-isometric-equiv-Metric-Space e =
    is-section-map-inv-equiv (equiv-isometric-equiv-Metric-Space e)

  is-retraction-map-inv-isometric-equiv-Metric-Space :
    (e : isometric-equiv-Metric-Space) →
    is-retraction
      ( map-isometric-equiv-Metric-Space e)
      ( map-inv-isometric-equiv-Metric-Space e)
  is-retraction-map-inv-isometric-equiv-Metric-Space e =
    is-retraction-map-inv-equiv (equiv-isometric-equiv-Metric-Space e)

  is-isometry-map-isometric-equiv-Metric-Space :
    (e : isometric-equiv-Metric-Space) →
    is-isometry-Metric-Space A B (map-isometric-equiv-Metric-Space e)
  is-isometry-map-isometric-equiv-Metric-Space = pr2
```

### Isometric equivalences between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometric-equiv-Metric-Space' : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Metric-Space' =
    isometric-equiv-Pseudometric-Space'
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

## Properties

### Equality of metric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-eq-isometric-eq-Metric-Space :
    (A ＝ B) ≃ isometric-eq-Metric-Space A B
  equiv-eq-isometric-eq-Metric-Space =
    equiv-eq-isometric-eq-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B) ∘e
    ( extensionality-type-subtype'
      ( is-extensional-prop-Pseudometric-Space)
      ( A)
      ( B))

  eq-isometric-eq-Metric-Space :
    isometric-eq-Metric-Space A B → A ＝ B
  eq-isometric-eq-Metric-Space =
    map-inv-equiv equiv-eq-isometric-eq-Metric-Space
```

### Isometric equality is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-eq-Metric-Space :
      is-torsorial
        (λ (B : Metric-Space l1 l2) → isometric-eq-Metric-Space A B)
    is-torsorial-isometric-eq-Metric-Space =
      is-contr-equiv'
        ( Σ (Metric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-eq-Metric-Space A))
        ( is-torsorial-Id A)
```

### Isometric equality between the carrier types of metric spaces is equivalent isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-isometric-eq-equiv-Metric-Space :
    isometric-eq-Metric-Space A B ≃ isometric-equiv-Metric-Space A B
  equiv-isometric-eq-equiv-Metric-Space =
    equiv-isometric-eq-equiv-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

### Isometric equivalences of metric spaces characterize their equalities

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-eq-isometric-equiv-Metric-Space :
    (A ＝ B) ≃ isometric-equiv-Metric-Space A B
  equiv-eq-isometric-equiv-Metric-Space =
    ( equiv-isometric-eq-equiv-Metric-Space A B) ∘e
    ( equiv-eq-isometric-eq-Metric-Space A B)

  eq-isometric-equiv-Metric-Space :
    isometric-equiv-Metric-Space A B → A ＝ B
  eq-isometric-equiv-Metric-Space =
    map-inv-equiv
      ( equiv-eq-isometric-equiv-Metric-Space)
```

### Isometric equivalence of metric spaces is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-equiv-Metric-Space :
      is-torsorial
        (λ (B : Metric-Space l1 l2) → isometric-equiv-Metric-Space A B)
    is-torsorial-isometric-equiv-Metric-Space =
      is-contr-equiv'
        ( Σ (Metric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-equiv-Metric-Space A))
        ( is-torsorial-Id A)
```

### Two metric spaces are isometrically equivalent if and only if there is an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-isometric-equiv-isometric-equiv-Metric-Space' :
    isometric-equiv-Metric-Space A B ≃ isometric-equiv-Metric-Space' A B
  equiv-isometric-equiv-isometric-equiv-Metric-Space' =
    equiv-isometric-equiv-isometric-equiv-Pseudometric-Space'
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

### Isometric equivalences between metric spaces characterize their equality

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-eq-isometric-equiv-Metric-Space' :
    (A ＝ B) ≃ isometric-equiv-Metric-Space' A B
  equiv-eq-isometric-equiv-Metric-Space' =
    ( equiv-isometric-equiv-isometric-equiv-Metric-Space' A B) ∘e
    ( equiv-eq-isometric-equiv-Metric-Space A B)

  eq-isometric-equiv-Metric-Space' :
    isometric-equiv-Metric-Space' A B → A ＝ B
  eq-isometric-equiv-Metric-Space' =
    map-inv-equiv equiv-eq-isometric-equiv-Metric-Space'
```

### The existence of invertible isometries between metric spaces is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-equiv-Metric-Space' :
      is-torsorial
        (λ (B : Metric-Space l1 l2) → isometric-equiv-Metric-Space' A B)
    is-torsorial-isometric-equiv-Metric-Space' =
      is-contr-equiv'
        ( Σ (Metric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-equiv-Metric-Space' A))
        ( is-torsorial-Id A)
```
