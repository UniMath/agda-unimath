# Isometric equivalences between premetric spaces

```agda
module metric-spaces.isometric-equivalences-premetric-spaces where
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

open import metric-spaces.isometric-equivalent-premetric-spaces
open import metric-spaces.isometry-premetric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

A function between [premetric spaces](metric-spaces.premetric-spaces.md) is an
{{#concept "isometric equivalence" Disambiguation="between premetric spaces" Agda=is-isometric-is-equiv-Premetric-Space}}
if it is both an [equivalence](foundation.equivalences.md) and an
[isometry](metric-spaces.isometry-premetric-spaces.md).

Isometric equivalences characterize the equality of premetric spaces.

## Definitions

### The type of isometric invertible maps between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  is-isometric-is-equiv-prop-Premetric-Space :
    (f : function-carrier-type-Premetric-Space A B) → Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometric-is-equiv-prop-Premetric-Space f =
    product-Prop
      ( is-equiv-Prop f)
      ( is-isometry-prop-Premetric-Space A B f)

  is-isometric-is-equiv-Premetric-Space :
    (f : function-carrier-type-Premetric-Space A B) → UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometric-is-equiv-Premetric-Space f =
    type-Prop (is-isometric-is-equiv-prop-Premetric-Space f)

  is-prop-is-isometric-is-equiv-Premetric-Space :
    (f : function-carrier-type-Premetric-Space A B) →
    is-prop (is-isometric-is-equiv-Premetric-Space f)
  is-prop-is-isometric-is-equiv-Premetric-Space f =
    is-prop-type-Prop (is-isometric-is-equiv-prop-Premetric-Space f)

  isometric-is-equiv-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-is-equiv-Premetric-Space =
    type-subtype is-isometric-is-equiv-prop-Premetric-Space
```

## Properties

### Two premetric spaces are isometrically equivalent if and only if there is an isometric invertible map between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometric-is-equiv-isometric-equiv-Premetric-Space :
    isometric-equiv-Premetric-Space A B ≃ isometric-is-equiv-Premetric-Space A B
  equiv-isometric-is-equiv-isometric-equiv-Premetric-Space =
    equiv-tot
      ( λ f →
        equiv-tot
          ( λ e →
            equiv-eq (ap (is-isometry-Premetric-Space A B) refl))) ∘e
    associative-Σ
      ( function-carrier-type-Premetric-Space A B)
      ( is-equiv)
      ( is-isometric-equiv-Premetric-Space A B)
```

### Equality of premetric types is equivalent to the existence of an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometric-is-equiv-eq-Premetric-Space :
    (A ＝ B) ≃ isometric-is-equiv-Premetric-Space A B
  equiv-isometric-is-equiv-eq-Premetric-Space =
    equiv-isometric-is-equiv-isometric-equiv-Premetric-Space A B ∘e
    equiv-isometric-equiv-eq-Premetric-Space A B
```

### Isometric equivalence of maps between premetric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-torsorial-isometric-is-equiv-Premetric-Space :
    is-torsorial (isometric-is-equiv-Premetric-Space A)
  is-torsorial-isometric-is-equiv-Premetric-Space =
    is-contr-equiv'
      ( Σ (Premetric-Space l1 l2) (isometric-equiv-Premetric-Space A))
      ( equiv-tot (equiv-isometric-is-equiv-isometric-equiv-Premetric-Space A))
      ( is-torsorial-isometric-equiv-Premetric-Space A)
```
