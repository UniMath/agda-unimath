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
open import metric-spaces.isometric-equivalences-premetric-spaces
open import metric-spaces.isometric-equivalent-premetric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

Equality of [metric-spaces](metric-spaces.metric-spaces.md) is equivalent to
[equality](metric-spaces.equality-of-premetric-spaces.md) of their carrier
[premetric spaces](metric-spaces.premetric-spaces.md); therefore,
{{#concept "isometric equality" Disambiguation="between metric spaces", Agda=isometric-eq-Metric-Space}}
between metric spaces characterizes their equality of metric spaces, as well as
[isometric equivalence](metric-spaces.isometric-equivalent-premetric-spaces.md),
or
[isometric equivalence maps](metric-spaces.isometric-equivalences-premetric-spaces.md)
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

  isometric-eq-Metric-Space : UU (lsuc l1 ⊔ l2 ⊔ l2')
  isometric-eq-Metric-Space =
    isometric-eq-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

### Isometric equivalence of metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometric-equiv-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Metric-Space =
    isometric-equiv-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

### Isometric equivalence maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  isometric-is-equiv-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-is-equiv-Metric-Space =
    isometric-is-equiv-Premetric-Space
      (premetric-Metric-Space A)
      (premetric-Metric-Space B)
```

## Properties

### Equality of metric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometric-eq-Metric-Space : (A ＝ B) ≃ isometric-eq-Metric-Space A B
  equiv-isometric-eq-Metric-Space =
    ( equiv-isometric-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometric-eq-Metric-Space : isometric-eq-Metric-Space A B → A ＝ B
  eq-isometric-eq-Metric-Space = map-inv-equiv equiv-isometric-eq-Metric-Space
```

### Isometric equality is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometric-eq-Metric-Space :
    is-torsorial (isometric-eq-Metric-Space A)
  is-torsorial-isometric-eq-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometric-eq-Metric-Space A))
      ( is-torsorial-Id A)
```

### Equality of metric spaces is equivalent to isometric equivalence of their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometric-equiv-Metric-Space :
    (A ＝ B) ≃ isometric-equiv-Metric-Space A B
  equiv-isometric-equiv-Metric-Space =
    ( equiv-isometric-equiv-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometric-equiv-Metric-Space : isometric-equiv-Metric-Space A B → A ＝ B
  eq-isometric-equiv-Metric-Space =
    map-inv-equiv equiv-isometric-equiv-Metric-Space
```

### Isometric equivalence between metric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometric-equiv-Metric-Space :
    is-torsorial (isometric-equiv-Metric-Space A)
  is-torsorial-isometric-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometric-equiv-Metric-Space A))
      ( is-torsorial-Id A)
```

### Equality of metric spaces is equivalent to the existence of isometric equivalence maps between their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-isometric-is-equiv-Metric-Space :
    (A ＝ B) ≃ isometric-is-equiv-Metric-Space A B
  equiv-isometric-is-equiv-Metric-Space =
    ( equiv-isometric-is-equiv-eq-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)) ∘e
    ( equiv-eq-premetric-Metric-Space A B)

  eq-isometric-is-equiv-Metric-Space :
    isometric-is-equiv-Metric-Space A B → A ＝ B
  eq-isometric-is-equiv-Metric-Space =
    map-inv-equiv equiv-isometric-is-equiv-Metric-Space
```

### Isometric equivalence between metric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-isometric-is-equiv-Metric-Space :
    is-torsorial (isometric-is-equiv-Metric-Space A)
  is-torsorial-isometric-is-equiv-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometric-is-equiv-Metric-Space A))
      ( is-torsorial-Id A)
```
