# Pointed type duality

```agda
module structured-types.pointed-type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections

open import structured-types.equivalences-retractive-types
open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.retractive-types
```

</details>

## Idea

Families of [pointed types](structured-types.pointed-types.md) over `X` are
[equivalent](foundation-core.equivalences.md) to
[retractive types](structured-types.retractive-types.md) under `X`.

## Definitions

### The family of pointed types associated to a retractive type

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : Retractive-Type l2 X)
  where

  fam-Retractive-Type : X → UU (l1 ⊔ l2)
  fam-Retractive-Type = fiber (map-retraction-Retractive-Type A)

  point-fam-Retractive-Type : (x : X) → fam-Retractive-Type x
  point-fam-Retractive-Type x =
    ( inclusion-Retractive-Type A x , is-retract-Retractive-Type A x)

  fam-pointed-type-Retractive-Type : X → Pointed-Type (l1 ⊔ l2)
  fam-pointed-type-Retractive-Type x =
    ( fam-Retractive-Type x , point-fam-Retractive-Type x)
```

### The retractive type associated to a family of pointed types

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : X → Pointed-Type l2)
  where

  type-retractive-type-Fam-Pointed-Type : UU (l1 ⊔ l2)
  type-retractive-type-Fam-Pointed-Type = Σ X (type-Pointed-Type ∘ A)

  map-inclusion-retractive-type-Fam-Pointed-Type :
    X → type-retractive-type-Fam-Pointed-Type
  map-inclusion-retractive-type-Fam-Pointed-Type x =
    ( x , point-Pointed-Type (A x))

  map-retraction-retractive-type-Fam-Pointed-Type :
    type-retractive-type-Fam-Pointed-Type → X
  map-retraction-retractive-type-Fam-Pointed-Type = pr1

  is-retract-retractive-type-Fam-Pointed-Type :
    is-retraction
      map-inclusion-retractive-type-Fam-Pointed-Type
      map-retraction-retractive-type-Fam-Pointed-Type
  is-retract-retractive-type-Fam-Pointed-Type = refl-htpy

  retraction-retractive-type-Fam-Pointed-Type :
    retraction map-inclusion-retractive-type-Fam-Pointed-Type
  retraction-retractive-type-Fam-Pointed-Type =
    ( map-retraction-retractive-type-Fam-Pointed-Type ,
      is-retract-retractive-type-Fam-Pointed-Type)

  retract-retractive-type-Fam-Pointed-Type :
    X retract-of type-retractive-type-Fam-Pointed-Type
  retract-retractive-type-Fam-Pointed-Type =
    ( map-inclusion-retractive-type-Fam-Pointed-Type ,
      retraction-retractive-type-Fam-Pointed-Type)

  retractive-type-Fam-Pointed-Type : Retractive-Type (l1 ⊔ l2) X
  retractive-type-Fam-Pointed-Type =
    ( type-retractive-type-Fam-Pointed-Type ,
      retract-retractive-type-Fam-Pointed-Type)
```

## Properties

### Retractive types under `X` are equivalent to families of pointed types over `X`

```agda
fam-pointed-equiv-is-section-retractive-type-Fam-Pointed-Type :
  {l1 l2 : Level} {X : UU l1} (A : (x : X) → Pointed-Type l2) →
  (x : X) →
  fam-pointed-type-Retractive-Type X (retractive-type-Fam-Pointed-Type X A) x ≃∗
  A x
fam-pointed-equiv-is-section-retractive-type-Fam-Pointed-Type A x =
  ( ( ( λ ((x' , a) , p) → tr (type-Pointed-Type ∘ A) p a) ,
      ( is-equiv-is-invertible
        ( λ a → (x , a) , refl)
        ( refl-htpy)
        ( λ where ((x' , a) , refl) → refl))) ,
    ( refl))

module _
  {l1 l2 : Level} {X : UU l1}
  where

  abstract
    is-section-retractive-type-Fam-Pointed-Type :
      is-section
        ( fam-pointed-type-Retractive-Type {l2 = l1 ⊔ l2} X)
        ( retractive-type-Fam-Pointed-Type X)
    is-section-retractive-type-Fam-Pointed-Type A =
      eq-htpy
        ( λ x →
          eq-pointed-equiv
            ( fam-pointed-type-Retractive-Type X
              ( retractive-type-Fam-Pointed-Type X A)
              ( x))
            ( A x)
            ( fam-pointed-equiv-is-section-retractive-type-Fam-Pointed-Type A
              ( x)))

  is-retraction-retractive-type-Fam-Pointed-Type :
    is-retraction
      ( fam-pointed-type-Retractive-Type {l2 = l1 ⊔ l2} X)
      ( retractive-type-Fam-Pointed-Type X)
  is-retraction-retractive-type-Fam-Pointed-Type A =
    eq-equiv-Retractive-Type'
      ( retractive-type-Fam-Pointed-Type X
        ( fam-pointed-type-Retractive-Type X A))
      ( A)
      ( ( equiv-total-fiber (map-retraction-Retractive-Type A)) ,
        ( refl-htpy) ,
        ( pr2 ∘ pr2) ,
        ( inv-htpy-right-unit-htpy))

  is-equiv-fam-pointed-type-Retractive-Type :
    is-equiv (fam-pointed-type-Retractive-Type {l2 = l1 ⊔ l2} X)
  is-equiv-fam-pointed-type-Retractive-Type =
      is-equiv-is-invertible
        ( retractive-type-Fam-Pointed-Type X)
        ( is-section-retractive-type-Fam-Pointed-Type)
        ( is-retraction-retractive-type-Fam-Pointed-Type)

  is-equiv-retractive-type-Fam-Pointed-Type :
    is-equiv (retractive-type-Fam-Pointed-Type {l2 = l1 ⊔ l2} X)
  is-equiv-retractive-type-Fam-Pointed-Type =
      is-equiv-is-invertible
        ( fam-pointed-type-Retractive-Type X)
        ( is-retraction-retractive-type-Fam-Pointed-Type)
        ( is-section-retractive-type-Fam-Pointed-Type)

  equiv-retractive-type-Fam-Pointed-Type :
    (X → Pointed-Type (l1 ⊔ l2)) ≃ Retractive-Type (l1 ⊔ l2) X
  equiv-retractive-type-Fam-Pointed-Type =
    ( retractive-type-Fam-Pointed-Type X ,
      is-equiv-retractive-type-Fam-Pointed-Type)

  equiv-fam-pointed-type-Retractive-Type :
    Retractive-Type (l1 ⊔ l2) X ≃ (X → Pointed-Type (l1 ⊔ l2))
  equiv-fam-pointed-type-Retractive-Type =
    ( fam-pointed-type-Retractive-Type X ,
      is-equiv-fam-pointed-type-Retractive-Type)
```
