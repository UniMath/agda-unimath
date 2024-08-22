# Isometric equivalent metric spaces

```agda
module metric-spaces.isometric-equivalent-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

An [equivalence](foundation.equivalences.md) between the carrier types of two
[metric spaces](metric-spaces.metric-spaces.md) is
{{#concept "isometric" Disambiguation="equivalence between metric spaces" Agda=is-isometric-equic-Metric-Space}}
if its carrier map is an [isometry](metric-spaces.isometry-metric-spaces.md).

Isometric equivalnces characterize the equality of metric spaces.

## Definitions

### Isometrically equivalent metric spaces

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  is-isometric-equiv-prop-Metric-Space :
    (e : type-Metric-Space A ≃ type-Metric-Space B) → Prop l
  is-isometric-equiv-prop-Metric-Space e =
    is-isometry-prop-function-Metric-Space A B (map-equiv e)

  is-isometric-equiv-Metric-Space :
    (e : type-Metric-Space A ≃ type-Metric-Space B) → UU l
  is-isometric-equiv-Metric-Space e =
    type-Prop (is-isometric-equiv-prop-Metric-Space e)

  is-prop-is-isometric-equiv-Metric-Space :
    (e : type-Metric-Space A ≃ type-Metric-Space B) →
    is-prop (is-isometric-equiv-Metric-Space e)
  is-prop-is-isometric-equiv-Metric-Space e =
    is-prop-type-Prop (is-isometric-equiv-prop-Metric-Space e)

  isometric-equiv-Metric-Space : UU l
  isometric-equiv-Metric-Space =
    type-subtype is-isometric-equiv-prop-Metric-Space
```

## Properties

### Isometric equivalence of metric spaces is equivalent to equality

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  equiv-isometric-eq-equiv-Metric-Space :
    isometric-eq-Metric-Space A B ≃ isometric-equiv-Metric-Space A B
  equiv-isometric-eq-equiv-Metric-Space =
    equiv-Σ
      ( λ e → is-isometry-function-Metric-Space A B (map-equiv e))
      ( equiv-univalence)
      ( λ (e : type-Metric-Space A ＝ type-Metric-Space B) →
        equiv-eq
          (ap (is-isometry-function-Metric-Space A B) (eq-htpy (λ x → refl))))

  equiv-isometric-equiv-eq-Metric-Space :
    (A ＝ B) ≃ isometric-equiv-Metric-Space A B
  equiv-isometric-equiv-eq-Metric-Space =
    equiv-isometric-eq-equiv-Metric-Space ∘e equiv-isometric-eq-Metric-Space A B
```

### Isometric equivalence of metric spaces is torsorial

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-torsorial-isometric-equiv-Metric-Space :
    is-torsorial (isometric-equiv-Metric-Space A)
  is-torsorial-isometric-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l) (isometric-eq-Metric-Space A))
      ( equiv-tot (equiv-isometric-eq-equiv-Metric-Space A))
      ( is-torsorial-isometric-eq-Metric-Space A)
```
