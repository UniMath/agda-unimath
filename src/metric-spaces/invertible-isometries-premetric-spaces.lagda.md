# Invertible isometries between premetric spaces

```agda
module metric-spaces.invertible-isometries-premetric-spaces where
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

open import metric-spaces.isometric-equivalences-premetric-spaces
open import metric-spaces.isometries-premetric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

A function between [premetric spaces](metric-spaces.premetric-spaces.md) is an
{{#concept "invertible isometry" Disambiguation="between premetric spaces" Agda=is-isometry-is-equiv-Premetric-Space}}
if it is both an [equivalence](foundation.equivalences.md) and an
[isometry](metric-spaces.isometries-premetric-spaces.md). Invertible isometries
characterize the equality of premetric spaces.

## Definitions

### The type of invertible isometries between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  is-isometry-is-equiv-prop-Premetric-Space :
    (f : map-type-Premetric-Space A B) → Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometry-is-equiv-prop-Premetric-Space f =
    product-Prop
      ( is-equiv-Prop f)
      ( is-isometry-prop-Premetric-Space A B f)

  is-isometry-is-equiv-Premetric-Space :
    (f : map-type-Premetric-Space A B) → UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometry-is-equiv-Premetric-Space f =
    type-Prop (is-isometry-is-equiv-prop-Premetric-Space f)

  is-prop-is-isometry-is-equiv-Premetric-Space :
    (f : map-type-Premetric-Space A B) →
    is-prop (is-isometry-is-equiv-Premetric-Space f)
  is-prop-is-isometry-is-equiv-Premetric-Space f =
    is-prop-type-Prop (is-isometry-is-equiv-prop-Premetric-Space f)

  isometry-is-equiv-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-is-equiv-Premetric-Space =
    type-subtype is-isometry-is-equiv-prop-Premetric-Space
```

## Properties

### Two premetric spaces are isometrically equivalent if and only if there is an invertible isometry between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometry-is-equiv-isometry-equiv-Premetric-Space :
    isometry-equiv-Premetric-Space A B ≃ isometry-is-equiv-Premetric-Space A B
  equiv-isometry-is-equiv-isometry-equiv-Premetric-Space =
    equiv-tot
      ( λ f →
        equiv-tot
          ( λ e →
            equiv-eq (ap (is-isometry-Premetric-Space A B) refl))) ∘e
    associative-Σ
      ( map-type-Premetric-Space A B)
      ( is-equiv)
      ( is-isometry-equiv-Premetric-Space A B)
```

### Equality of premetric types is equivalent to the existence of an invertible isometry between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometry-is-equiv-eq-Premetric-Space :
    (A ＝ B) ≃ isometry-is-equiv-Premetric-Space A B
  equiv-isometry-is-equiv-eq-Premetric-Space =
    equiv-isometry-is-equiv-isometry-equiv-Premetric-Space A B ∘e
    equiv-isometry-equiv-eq-Premetric-Space A B
```

### The existence of invertible isometries between premetric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-torsorial-isometry-is-equiv-Premetric-Space :
    is-torsorial (isometry-is-equiv-Premetric-Space A)
  is-torsorial-isometry-is-equiv-Premetric-Space =
    is-contr-equiv'
      ( Σ (Premetric-Space l1 l2) (isometry-equiv-Premetric-Space A))
      ( equiv-tot (equiv-isometry-is-equiv-isometry-equiv-Premetric-Space A))
      ( is-torsorial-isometry-equiv-Premetric-Space A)
```
