# Equality of metric spaces

```agda
module metric-spaces.equality-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.equality-of-premetric-spaces
open import metric-spaces.invertible-isometries-premetric-spaces
open import metric-spaces.isometric-equivalences-premetric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

Equality of [metric spaces](metric-spaces.metric-spaces.md) is equivalent to
[equality](metric-spaces.equality-of-premetric-spaces.md) of their carrier
[premetric spaces](metric-spaces.premetric-spaces.md); therefore,
{{#concept "isometric equality" Disambiguation="between metric spaces", Agda=isometry-eq-Metric-Space}}
between metric spaces characterizes their equality, as well as
[isometric equivalence](metric-spaces.isometric-equivalences-premetric-spaces.md),
and
[invertible isometries](metric-spaces.invertible-isometries-premetric-spaces.md)
between their carrier premetric spaces.

## Definitions

### Equality of metric spaces is equivalent to equality of their carrier premetric spaces

```agda
module _
  {l1 l2 : Level}
  (A B : Metric-Space l1 l2)
  where

  equiv-eq-premetric-Metric-Space :
    (A ＝ B) ≃ (premetric-Metric-Space A ＝ premetric-Metric-Space B)
  equiv-eq-premetric-Metric-Space =
    extensionality-type-subtype' is-metric-prop-Premetric-Space A B
```

### Isometric equality of metric spaces

```agda
module _
  {l1 l2 l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1 l2')
  where

  isometry-eq-Metric-Space : UU (lsuc l1 ⊔ l2 ⊔ l2')
  isometry-eq-Metric-Space =
    isometry-eq-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

### Isometric equivalence of metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometry-equiv-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-equiv-Metric-Space =
    isometry-equiv-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

### Invertible isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometry-is-equiv-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-is-equiv-Metric-Space =
    isometry-is-equiv-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

## Properties

### Equality of metric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometry-eq-Metric-Space : (A ＝ B) ≃ isometry-eq-Metric-Space A B
  equiv-isometry-eq-Metric-Space =
    ( equiv-isometry-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometry-eq-Metric-Space : isometry-eq-Metric-Space A B → A ＝ B
  eq-isometry-eq-Metric-Space = map-inv-equiv equiv-isometry-eq-Metric-Space
```

### Isometric equality is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometry-eq-Metric-Space :
    is-torsorial (isometry-eq-Metric-Space A)
  is-torsorial-isometry-eq-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometry-eq-Metric-Space A))
      ( is-torsorial-Id A)
```

### Equality of metric spaces is equivalent to isometric equivalence of their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometry-equiv-eq-Metric-Space :
    (A ＝ B) ≃ isometry-equiv-Metric-Space A B
  equiv-isometry-equiv-eq-Metric-Space =
    ( equiv-isometry-equiv-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometry-equiv-Metric-Space : isometry-equiv-Metric-Space A B → A ＝ B
  eq-isometry-equiv-Metric-Space =
    map-inv-equiv equiv-isometry-equiv-eq-Metric-Space
```

### Isometric equivalence between metric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometry-equiv-Metric-Space :
    is-torsorial (isometry-equiv-Metric-Space A)
  is-torsorial-isometry-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometry-equiv-eq-Metric-Space A))
      ( is-torsorial-Id A)
```

### Equality of metric spaces is equivalent to the existence of invertible isometry between their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometry-is-equiv-Metric-Space :
    (A ＝ B) ≃ isometry-is-equiv-Metric-Space A B
  equiv-isometry-is-equiv-Metric-Space =
    ( equiv-isometry-is-equiv-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometry-is-equiv-Metric-Space :
    isometry-is-equiv-Metric-Space A B → A ＝ B
  eq-isometry-is-equiv-Metric-Space =
    map-inv-equiv equiv-isometry-is-equiv-Metric-Space
```

### The existence of invertibe isometries between metric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometry-is-equiv-Metric-Space :
    is-torsorial (isometry-is-equiv-Metric-Space A)
  is-torsorial-isometry-is-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometry-is-equiv-Metric-Space A))
      ( is-torsorial-Id A)
```
