# Equality of pseudometric spaces

```agda
module metric-spaces.equality-of-pseudometric-spaces where
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
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

[Equality](foundation-core.identity-types.md) of
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) is characterized by
the following equivalent concepts:

- an [equality](foundation-core.identity-types.md) between their carrier types
  such that the induced map under [`map-eq`](foundation-core.univalence.md) is
  an [isometry](metric-spaces.isometries-pseudometric-spaces.md);

- an [equivalence](foundation-core.equivalences.md) between their carrier types
  such that the induced map under [`map-equiv`](foundation-core.equivalences.md)
  is an [isometry](metric-spaces.isometries-pseudometric-spaces.md);

- a function between their carrier types that is both an
  [equivalence](foundation-core.equivalences.md) and an
  [isometry](metric-spaces.isometries-pseudometric-spaces.md).

## Definitions

### Isometric equality of pseudometric spaces

```agda
module _
  {l1 l2 l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1 l2')
  where

  isometric-eq-Pseudometric-Space : UU (lsuc l1 ⊔ l2 ⊔ l2')
  isometric-eq-Pseudometric-Space =
    Σ (type-Pseudometric-Space A ＝ type-Pseudometric-Space B)
      (λ e → is-isometry-Pseudometric-Space A B (map-eq e))
```

### Isometric equivalence of pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  isometric-equiv-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Pseudometric-Space =
    Σ (type-Pseudometric-Space A ≃ type-Pseudometric-Space B)
      (λ e → is-isometry-Pseudometric-Space A B (map-equiv e))
```

### Isometric equivalences between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  isometric-equiv-Pseudometric-Space' : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometric-equiv-Pseudometric-Space' =
    Σ (type-function-Pseudometric-Space A B)
      (λ f → (is-equiv f) × (is-isometry-Pseudometric-Space A B f))
```

## Properties

### Equality of pseudometric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l1 l2 : Level}
  (A B : Pseudometric-Space l1 l2)
  where

  equiv-eq-isometric-eq-Pseudometric-Space :
    (A ＝ B) ≃ isometric-eq-Pseudometric-Space A B
  equiv-eq-isometric-eq-Pseudometric-Space =
    ( equiv-tot
      ( equiv-Eq-tr-Pseudometric-Structure
        ( type-Pseudometric-Space A)
        ( type-Pseudometric-Space B)
        ( structure-Pseudometric-Space A)
        ( structure-Pseudometric-Space B))) ∘e
    ( equiv-pair-eq-Σ A B)

  eq-isometric-eq-Pseudometric-Space :
    isometric-eq-Pseudometric-Space A B → A ＝ B
  eq-isometric-eq-Pseudometric-Space =
    map-inv-equiv equiv-eq-isometric-eq-Pseudometric-Space
```

### Isometric equality is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Pseudometric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-eq-Pseudometric-Space :
      is-torsorial
        ( λ ( B : Pseudometric-Space l1 l2) →
            ( isometric-eq-Pseudometric-Space A B))
    is-torsorial-isometric-eq-Pseudometric-Space =
      is-contr-equiv'
        ( Σ (Pseudometric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-eq-Pseudometric-Space A))
        ( is-torsorial-Id A)
```

### Isometric equality between the carrier types of pseudometric spaces is equivalent to isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Pseudometric-Space l1 l2)
  where

  equiv-isometric-eq-equiv-Pseudometric-Space :
    isometric-eq-Pseudometric-Space A B ≃ isometric-equiv-Pseudometric-Space A B
  equiv-isometric-eq-equiv-Pseudometric-Space =
    equiv-Σ
      ( λ e → is-isometry-Pseudometric-Space A B (map-equiv e))
      ( equiv-univalence)
      ( λ (e : type-Pseudometric-Space A ＝ type-Pseudometric-Space B) →
        equiv-eq
          (ap (is-isometry-Pseudometric-Space A B) (eq-htpy refl-htpy)))
```

### Isometric equivalences of pseudometric spaces characterize their equality

```agda
module _
  {l1 l2 : Level}
  (A B : Pseudometric-Space l1 l2)
  where

  equiv-eq-isometric-equiv-Pseudometric-Space :
    (A ＝ B) ≃ isometric-equiv-Pseudometric-Space A B
  equiv-eq-isometric-equiv-Pseudometric-Space =
    ( equiv-isometric-eq-equiv-Pseudometric-Space A B) ∘e
    ( equiv-eq-isometric-eq-Pseudometric-Space A B)
```

### Isometric equivalence of pseudometric spaces is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Pseudometric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-equiv-Pseudometric-Space :
      is-torsorial
        ( λ (B : Pseudometric-Space l1 l2) →
          isometric-equiv-Pseudometric-Space A B)
    is-torsorial-isometric-equiv-Pseudometric-Space =
      is-contr-equiv'
        ( Σ (Pseudometric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-equiv-Pseudometric-Space A))
        ( is-torsorial-Id A)
```

### Two pseudometric spaces are isometrically equivalent if and only if there is an isometric equivalence between them

```agda
module _
  {l1 l2 : Level}
  (A B : Pseudometric-Space l1 l2)
  where

  equiv-isometric-equiv-isometric-equiv-Pseudometric-Space' :
    isometric-equiv-Pseudometric-Space A B ≃
    isometric-equiv-Pseudometric-Space' A B
  equiv-isometric-equiv-isometric-equiv-Pseudometric-Space' =
    ( equiv-tot
      ( λ f →
        equiv-tot
          ( λ e →
            equiv-eq (ap (is-isometry-Pseudometric-Space A B) refl)))) ∘e
    ( associative-Σ
      ( type-function-Pseudometric-Space A B)
      ( is-equiv)
      ( is-isometry-Pseudometric-Space A B ∘ map-equiv))
```

### Isometric equivalences between pseudometric spaces characterize their equality

```agda
module _
  {l1 l2 : Level}
  (A B : Pseudometric-Space l1 l2)
  where

  equiv-eq-isometric-equiv-Pseudometric-Space' :
    (A ＝ B) ≃ isometric-equiv-Pseudometric-Space' A B
  equiv-eq-isometric-equiv-Pseudometric-Space' =
    ( equiv-isometric-equiv-isometric-equiv-Pseudometric-Space' A B) ∘e
    ( equiv-eq-isometric-equiv-Pseudometric-Space A B)

  eq-isometric-equiv-Pseudometric-Space' :
    isometric-equiv-Pseudometric-Space' A B → A ＝ B
  eq-isometric-equiv-Pseudometric-Space' =
    map-inv-equiv equiv-eq-isometric-equiv-Pseudometric-Space'
```

### Invertible isometry between pseudometric spaces is torsorial

```agda
module _
  {l1 l2 : Level}
  (A : Pseudometric-Space l1 l2)
  where

  abstract
    is-torsorial-isometric-equiv-Pseudometric-Space' :
      is-torsorial
        ( λ ( B : Pseudometric-Space l1 l2) →
            ( isometric-equiv-Pseudometric-Space' A B))
    is-torsorial-isometric-equiv-Pseudometric-Space' =
      is-contr-equiv'
        ( Σ (Pseudometric-Space l1 l2) (Id A))
        ( equiv-tot (equiv-eq-isometric-equiv-Pseudometric-Space' A))
        ( is-torsorial-Id A)
```
