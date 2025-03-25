# Isometric equivalences between premetric spaces

```agda
module metric-spaces.isometric-equivalences-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.equality-of-premetric-spaces
open import metric-spaces.isometries-premetric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

An [equivalence](foundation.equivalences.md) between the carrier types of two
[premetric spaces](metric-spaces.premetric-spaces.md) is
{{#concept "isometric" Disambiguation="equivalence between premetric spaces" Agda=is-isometry-equiv-Premetric-Space}}
if its carrier map is an
[isometry](metric-spaces.isometries-premetric-spaces.md). Isometric equivalences
between premetric spaces characterize their equality.

## Definitions

### Isometrically equivalent premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  is-isometry-equiv-prop-Premetric-Space :
    (e : type-Premetric-Space A ≃ type-Premetric-Space B) → Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-equiv-prop-Premetric-Space e =
    is-isometry-prop-Premetric-Space A B (map-equiv e)

  is-isometry-equiv-Premetric-Space :
    (e : type-Premetric-Space A ≃ type-Premetric-Space B) → UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-equiv-Premetric-Space e =
    type-Prop (is-isometry-equiv-prop-Premetric-Space e)

  is-prop-is-isometry-equiv-Premetric-Space :
    (e : type-Premetric-Space A ≃ type-Premetric-Space B) →
    is-prop (is-isometry-equiv-Premetric-Space e)
  is-prop-is-isometry-equiv-Premetric-Space e =
    is-prop-type-Prop (is-isometry-equiv-prop-Premetric-Space e)

  isometric-equiv-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Premetric-Space =
    type-subtype is-isometry-equiv-prop-Premetric-Space
```

### The type of isometric equivalences between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  is-isometric-equiv-prop-Premetric-Space :
    (f : map-type-Premetric-Space A B) → Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometric-equiv-prop-Premetric-Space f =
    product-Prop
      ( is-equiv-Prop f)
      ( is-isometry-prop-Premetric-Space A B f)

  is-isometric-equiv-Premetric-Space :
    (f : map-type-Premetric-Space A B) → UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-isometric-equiv-Premetric-Space f =
    type-Prop (is-isometric-equiv-prop-Premetric-Space f)

  is-prop-is-isometric-equiv-Premetric-Space :
    (f : map-type-Premetric-Space A B) →
    is-prop (is-isometric-equiv-Premetric-Space f)
  is-prop-is-isometric-equiv-Premetric-Space f =
    is-prop-type-Prop (is-isometric-equiv-prop-Premetric-Space f)

  isometric-equiv-Premetric-Space' : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Premetric-Space' =
    type-subtype is-isometric-equiv-prop-Premetric-Space
```

## Properties

### Two premetric spaces are isometrically equivalent if and only if there is an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometric-equiv-isometric-equiv-Premetric-Space' :
    isometric-equiv-Premetric-Space A B ≃ isometric-equiv-Premetric-Space' A B
  equiv-isometric-equiv-isometric-equiv-Premetric-Space' =
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

### Equality of premetric types is equivalent to the existence of an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Premetric-Space l1 l2)
  where

  equiv-isometric-eq-equiv-Premetric-Space :
    isometric-eq-Premetric-Space A B ≃ isometric-equiv-Premetric-Space A B
  equiv-isometric-eq-equiv-Premetric-Space =
    equiv-Σ
      ( λ e → is-isometry-Premetric-Space A B (map-equiv e))
      ( equiv-univalence)
      ( λ (e : type-Premetric-Space A ＝ type-Premetric-Space B) →
        equiv-eq
          (ap (is-isometry-Premetric-Space A B) (eq-htpy (λ x → refl))))

  equiv-isometric-equiv-eq-Premetric-Space :
    (A ＝ B) ≃ isometric-equiv-Premetric-Space A B
  equiv-isometric-equiv-eq-Premetric-Space =
    equiv-isometric-eq-equiv-Premetric-Space ∘e
    equiv-isometric-eq-eq-Premetric-Space A B

  equiv-isometric-equiv-eq-Premetric-Space' :
    (A ＝ B) ≃ isometric-equiv-Premetric-Space' A B
  equiv-isometric-equiv-eq-Premetric-Space' =
    equiv-isometric-equiv-isometric-equiv-Premetric-Space' A B ∘e
    equiv-isometric-equiv-eq-Premetric-Space
```

### Isometric equivalence of premetric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-torsorial-isometric-equiv-Premetric-Space :
    is-torsorial (isometric-equiv-Premetric-Space A)
  is-torsorial-isometric-equiv-Premetric-Space =
    is-contr-equiv'
      ( Σ (Premetric-Space l1 l2) (isometric-eq-Premetric-Space A))
      ( equiv-tot (equiv-isometric-eq-equiv-Premetric-Space A))
      ( is-torsorial-isometric-eq-Premetric-Space A)

  is-torsorial-isometric-equiv-Premetric-Space' :
    is-torsorial (isometric-equiv-Premetric-Space' A)
  is-torsorial-isometric-equiv-Premetric-Space' =
    is-contr-equiv'
      ( Σ (Premetric-Space l1 l2) (isometric-equiv-Premetric-Space A))
      ( equiv-tot (equiv-isometric-equiv-isometric-equiv-Premetric-Space' A))
      ( is-torsorial-isometric-equiv-Premetric-Space)
```
