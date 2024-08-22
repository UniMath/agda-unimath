# Isometric equivalences between metric spaces

```agda
module metric-spaces.isometric-equivalences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometric-equivalent-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between metric spaces is
an
{{#concept "isometric equivalence" Disambiguation="between metric spaces" Agda=is-isometric-is-equiv-Metric-Space}}
if it is both an [equivalence](foundation.equivalences.md) and an
[isometry](metric-spaces.isometry-metric-spaces.md).

Isometric equivalences characterize the identity type of metric spaces.

## Definitions

### The type of isometric invertible maps between metric spaces

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  is-isometric-is-equiv-prop-Metric-Space :
    (f : function-carrier-type-Metric-Space A B) → Prop l
  is-isometric-is-equiv-prop-Metric-Space f =
    product-Prop
      ( is-equiv-Prop f)
      ( is-isometry-prop-function-Metric-Space A B f)

  is-isometric-is-equiv-Metric-Space :
    (f : function-carrier-type-Metric-Space A B) → UU l
  is-isometric-is-equiv-Metric-Space f =
    type-Prop (is-isometric-is-equiv-prop-Metric-Space f)

  is-prop-is-isometric-is-equiv-Metric-Space :
    (f : function-carrier-type-Metric-Space A B) →
    is-prop (is-isometric-is-equiv-Metric-Space f)
  is-prop-is-isometric-is-equiv-Metric-Space f =
    is-prop-type-Prop (is-isometric-is-equiv-prop-Metric-Space f)

  isometric-is-equiv-Metric-Space : UU l
  isometric-is-equiv-Metric-Space =
    type-subtype is-isometric-is-equiv-prop-Metric-Space
```

## Properties

### Two spaces are isometrically equivalent if and only if there is an isometric invertible between them

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  equiv-isometric-is-equiv-isometric-equiv-Metric-Space :
    isometric-equiv-Metric-Space A B ≃ isometric-is-equiv-Metric-Space A B
  equiv-isometric-is-equiv-isometric-equiv-Metric-Space =
    equiv-tot
      ( λ f →
        equiv-tot
          ( λ e →
            equiv-eq (ap (is-isometry-function-Metric-Space A B) refl))) ∘e
    associative-Σ
      ( function-carrier-type-Metric-Space A B)
      ( is-equiv)
      ( is-isometric-equiv-Metric-Space A B)

  equiv-isometric-is-equiv-eq-Metric-Space :
    (A ＝ B) ≃ isometric-is-equiv-Metric-Space A B
  equiv-isometric-is-equiv-eq-Metric-Space =
    equiv-isometric-is-equiv-isometric-equiv-Metric-Space ∘e
    equiv-isometric-equiv-eq-Metric-Space A B
```

### Isometric equivalence between metric spaces is torsorial

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-torsorial-isometric-is-equiv-Metric-Space :
    is-torsorial (isometric-is-equiv-Metric-Space A)
  is-torsorial-isometric-is-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l) (isometric-equiv-Metric-Space A))
      ( equiv-tot (equiv-isometric-is-equiv-isometric-equiv-Metric-Space A))
      ( is-torsorial-isometric-equiv-Metric-Space A)
```
