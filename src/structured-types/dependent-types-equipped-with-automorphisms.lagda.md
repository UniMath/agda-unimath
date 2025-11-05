# Dependent types equipped with automorphisms

```agda
module structured-types.dependent-types-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.types-equipped-with-automorphisms
```

</details>

## Idea

Consider a
[type equipped with an automorphism](structured-types.types-equipped-with-automorphisms.md)
`(X, e)`. A
{{#concept "dependent type equipped with an automorphism" Agda=Dependent-Type-With-Automorphism}}
over `(X, e)` consists of a dependent type `Y` over `X` and for each `x : X` an
[equivalence](foundation-core.equivalences.md) `Y x ≃ Y (e x)`.

## Definitions

### Dependent types equipped with automorphisms

```agda
Dependent-Type-With-Automorphism :
  {l1 : Level} (l2 : Level) →
  Type-With-Automorphism l1 → UU (l1 ⊔ lsuc l2)
Dependent-Type-With-Automorphism l2 P =
  Σ ( type-Type-With-Automorphism P → UU l2)
    ( λ R → equiv-fam R (R ∘ (map-Type-With-Automorphism P)))

module _
  { l1 l2 : Level} (P : Type-With-Automorphism l1)
  ( Q : Dependent-Type-With-Automorphism l2 P)
  where

  family-Dependent-Type-With-Automorphism :
    type-Type-With-Automorphism P → UU l2
  family-Dependent-Type-With-Automorphism =
    pr1 Q

  dependent-automorphism-Dependent-Type-With-Automorphism :
    equiv-fam
      ( family-Dependent-Type-With-Automorphism)
      ( family-Dependent-Type-With-Automorphism ∘ map-Type-With-Automorphism P)
  dependent-automorphism-Dependent-Type-With-Automorphism = pr2 Q

  map-Dependent-Type-With-Automorphism :
    { x : type-Type-With-Automorphism P} →
    ( family-Dependent-Type-With-Automorphism x) →
    ( family-Dependent-Type-With-Automorphism (map-Type-With-Automorphism P x))
  map-Dependent-Type-With-Automorphism {x} =
    map-equiv (dependent-automorphism-Dependent-Type-With-Automorphism x)
```

### Equivalences of dependent types equipped with automorphisms

```agda
module _
  { l1 l2 l3 : Level} (P : Type-With-Automorphism l1)
  where

  equiv-Dependent-Type-With-Automorphism :
    Dependent-Type-With-Automorphism l2 P →
    Dependent-Type-With-Automorphism l3 P →
    UU (l1 ⊔ l2 ⊔ l3)
  equiv-Dependent-Type-With-Automorphism Q T =
    Σ ( equiv-fam
        ( family-Dependent-Type-With-Automorphism P Q)
        ( family-Dependent-Type-With-Automorphism P T))
      ( λ H →
        ( x : type-Type-With-Automorphism P) →
        coherence-square-maps
          ( map-equiv (H x))
          ( map-Dependent-Type-With-Automorphism P Q)
          ( map-Dependent-Type-With-Automorphism P T)
          ( map-equiv (H (map-Type-With-Automorphism P x))))

module _
  { l1 l2 l3 : Level} (P : Type-With-Automorphism l1)
  ( Q : Dependent-Type-With-Automorphism l2 P)
  ( T : Dependent-Type-With-Automorphism l3 P)
  ( α : equiv-Dependent-Type-With-Automorphism P Q T)
  where

  equiv-equiv-Dependent-Type-With-Automorphism :
    equiv-fam
      ( family-Dependent-Type-With-Automorphism P Q)
      ( family-Dependent-Type-With-Automorphism P T)
  equiv-equiv-Dependent-Type-With-Automorphism = pr1 α

  map-equiv-Dependent-Type-With-Automorphism :
    { x : type-Type-With-Automorphism P} →
    ( family-Dependent-Type-With-Automorphism P Q x) →
    ( family-Dependent-Type-With-Automorphism P T x)
  map-equiv-Dependent-Type-With-Automorphism {x} =
    map-equiv (equiv-equiv-Dependent-Type-With-Automorphism x)

  coherence-square-equiv-Dependent-Type-With-Automorphism :
    ( x : type-Type-With-Automorphism P) →
    coherence-square-maps
      ( map-equiv-Dependent-Type-With-Automorphism)
      ( map-Dependent-Type-With-Automorphism P Q)
      ( map-Dependent-Type-With-Automorphism P T)
      ( map-equiv-Dependent-Type-With-Automorphism)
  coherence-square-equiv-Dependent-Type-With-Automorphism = pr2 α
```

## Properties

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 : Level} (P : Type-With-Automorphism l1)
  where

  id-equiv-Dependent-Type-With-Automorphism :
    ( Q : Dependent-Type-With-Automorphism l2 P) →
    equiv-Dependent-Type-With-Automorphism P Q Q
  pr1 (id-equiv-Dependent-Type-With-Automorphism Q) =
    id-equiv-fam (family-Dependent-Type-With-Automorphism P Q)
  pr2 (id-equiv-Dependent-Type-With-Automorphism Q) x = refl-htpy

  equiv-eq-Dependent-Type-With-Automorphism :
    ( Q T : Dependent-Type-With-Automorphism l2 P) →
    Q ＝ T → equiv-Dependent-Type-With-Automorphism P Q T
  equiv-eq-Dependent-Type-With-Automorphism Q .Q refl =
    id-equiv-Dependent-Type-With-Automorphism Q

  is-torsorial-equiv-Dependent-Type-With-Automorphism :
    ( Q : Dependent-Type-With-Automorphism l2 P) →
    is-torsorial (equiv-Dependent-Type-With-Automorphism P Q)
  is-torsorial-equiv-Dependent-Type-With-Automorphism Q =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-fam (family-Dependent-Type-With-Automorphism P Q))
      ( family-Dependent-Type-With-Automorphism P Q ,
        id-equiv-fam (family-Dependent-Type-With-Automorphism P Q))
      ( is-torsorial-Eq-Π
        ( λ x →
          is-torsorial-htpy-equiv
            ( dependent-automorphism-Dependent-Type-With-Automorphism P Q x)))

  is-equiv-equiv-eq-Dependent-Type-With-Automorphism :
    ( Q T : Dependent-Type-With-Automorphism l2 P) →
    is-equiv (equiv-eq-Dependent-Type-With-Automorphism Q T)
  is-equiv-equiv-eq-Dependent-Type-With-Automorphism Q =
    fundamental-theorem-id
      ( is-torsorial-equiv-Dependent-Type-With-Automorphism Q)
      ( equiv-eq-Dependent-Type-With-Automorphism Q)

  extensionality-Dependent-Type-With-Automorphism :
    (Q T : Dependent-Type-With-Automorphism l2 P) →
    (Q ＝ T) ≃ equiv-Dependent-Type-With-Automorphism P Q T
  pr1 (extensionality-Dependent-Type-With-Automorphism Q T) =
    equiv-eq-Dependent-Type-With-Automorphism Q T
  pr2 (extensionality-Dependent-Type-With-Automorphism Q T) =
    is-equiv-equiv-eq-Dependent-Type-With-Automorphism Q T

  eq-equiv-Dependent-Type-With-Automorphism :
    ( Q T : Dependent-Type-With-Automorphism l2 P) →
    equiv-Dependent-Type-With-Automorphism P Q T → Q ＝ T
  eq-equiv-Dependent-Type-With-Automorphism Q T =
    map-inv-is-equiv (is-equiv-equiv-eq-Dependent-Type-With-Automorphism Q T)
```
