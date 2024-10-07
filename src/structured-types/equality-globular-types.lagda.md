# Equality of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.equality-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.equivalences
open import foundation-core.retractions
open import foundation-core.sections

open import structured-types.globular-types
```

</details>

## Idea

We postulate that [equality](foundation-core.identity-types.md) of
[globular types](structured-types.globular-types.md) is characterized by
equality of the 0-cells together with a binary family of equalities of the
globular type of 1-cells over the equality of the 0-cells. This phrasing is used
so that the extensionality principle is independent of
[univalence](foundation.univalence.md).

## Definitions

### Equality of globular types

```agda
module _
  {l1 l2 : Level}
  where

  Eq-Globular-Type : (A B : Globular-Type l1 l2) → UU (lsuc l1 ⊔ lsuc l2)
  Eq-Globular-Type A B =
    Σ ( 0-cell-Globular-Type A ＝ 0-cell-Globular-Type B)
      ( λ p →
        (x y : 0-cell-Globular-Type A) →
        1-cell-globular-type-Globular-Type A x y ＝
        1-cell-globular-type-Globular-Type B (map-eq p x) (map-eq p y))

  refl-Eq-Globular-Type : (A : Globular-Type l1 l2) → Eq-Globular-Type A A
  refl-Eq-Globular-Type A =
    ( refl , refl-binary-htpy (1-cell-globular-type-Globular-Type A))

  Eq-eq-Globular-Type :
    {A B : Globular-Type l1 l2} → A ＝ B → Eq-Globular-Type A B
  Eq-eq-Globular-Type {A} refl = refl-Eq-Globular-Type A
```

## Postulate

We postulate that the map `Eq-eq-Globular-Type : A ＝ B → Eq-Globular-Type A B`
is a [coherently invertible map](foundation-core.coherently-invertible-maps.md).

```agda
module _
  {l1 l2 : Level} {A B : Globular-Type l1 l2}
  where

  postulate
    eq-Eq-Globular-Type :
      Eq-Globular-Type A B → A ＝ B

  postulate
    is-section-eq-Eq-Globular-Type :
      is-section Eq-eq-Globular-Type eq-Eq-Globular-Type

  postulate
    is-retraction-eq-Eq-Globular-Type :
      is-retraction Eq-eq-Globular-Type eq-Eq-Globular-Type

  postulate
    coh-eq-Eq-Globular-Type :
      coherence-is-coherently-invertible
        ( Eq-eq-Globular-Type)
        ( eq-Eq-Globular-Type)
        ( is-section-eq-Eq-Globular-Type)
        ( is-retraction-eq-Eq-Globular-Type)
```

## Further definitions

```agda
module _
  {l1 l2 : Level} {A B : Globular-Type l1 l2}
  where

  is-coherently-invertible-Eq-eq-Globular-Type :
    is-coherently-invertible (Eq-eq-Globular-Type {A = A} {B})
  is-coherently-invertible-Eq-eq-Globular-Type =
    ( eq-Eq-Globular-Type ,
      is-section-eq-Eq-Globular-Type ,
      is-retraction-eq-Eq-Globular-Type ,
      coh-eq-Eq-Globular-Type)

  is-equiv-Eq-eq-Globular-Type : is-equiv (Eq-eq-Globular-Type {A = A} {B})
  is-equiv-Eq-eq-Globular-Type =
    is-equiv-is-invertible
      eq-Eq-Globular-Type
      is-section-eq-Eq-Globular-Type
      is-retraction-eq-Eq-Globular-Type

  is-equiv-eq-Eq-Globular-Type :
    is-equiv (eq-Eq-Globular-Type {A = A} {B})
  is-equiv-eq-Eq-Globular-Type =
    is-equiv-is-invertible
      Eq-eq-Globular-Type
      is-retraction-eq-Eq-Globular-Type
      is-section-eq-Eq-Globular-Type

  equiv-Eq-eq-Globular-Type : (A ＝ B) ≃ Eq-Globular-Type A B
  equiv-Eq-eq-Globular-Type = Eq-eq-Globular-Type , is-equiv-Eq-eq-Globular-Type

  equiv-eq-Eq-Globular-Type : Eq-Globular-Type A B ≃ (A ＝ B)
  equiv-eq-Eq-Globular-Type = eq-Eq-Globular-Type , is-equiv-eq-Eq-Globular-Type
```

### Characterization of equality of globular types in terms of equivalences

```agda
record
  equiv-Globular-Type
  {l1 l2 : Level} (A B : Globular-Type l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    0-cell-equiv-Globular-Type :
      0-cell-Globular-Type A ≃ 0-cell-Globular-Type B

  map-0-cell-equiv-Globular-Type :
    0-cell-Globular-Type A → 0-cell-Globular-Type B
  map-0-cell-equiv-Globular-Type =
    map-equiv 0-cell-equiv-Globular-Type

  field
    1-cell-equiv-Globular-Type :
      (x y : 0-cell-Globular-Type A) →
      equiv-Globular-Type
        ( 1-cell-globular-type-Globular-Type A x y)
        ( 1-cell-globular-type-Globular-Type B
          ( map-0-cell-equiv-Globular-Type x)
          ( map-0-cell-equiv-Globular-Type y))

open equiv-Globular-Type public
```
