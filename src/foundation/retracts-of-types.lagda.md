# Retracts of types

```agda
module foundation.retracts-of-types where

open import foundation-core.retracts-of-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.precomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

We say that a type `A` is a **retract of** a type `B` if the types `A` and `B`
come equipped with **retract data**, i.e., with maps

```text
      i        r
  A -----> B -----> A
```

and a [homotopy](foundation-core.homotopies.md) `r ∘ i ~ id`. The map `i` is
called the **inclusion** of the retract data, and the map `r` is called the
**underlying map of the retraction**.

## Properties

### Characterizing equality of retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-htpy-retract :
    (R S : A retract-of B)
    (I : inclusion-retract R ~ inclusion-retract S)
    (H : map-retraction-retract R ~ map-retraction-retract S) →
    UU l1
  coherence-htpy-retract R S I H =
    ( is-retraction-map-retraction-retract R) ~
    ( horizontal-concat-htpy H I ∙h is-retraction-map-retraction-retract S)

  htpy-retract : (R S : A retract-of B) → UU (l1 ⊔ l2)
  htpy-retract R S =
    Σ ( inclusion-retract R ~ inclusion-retract S)
      ( λ I →
        Σ ( map-retraction-retract R ~ map-retraction-retract S)
          ( coherence-htpy-retract R S I))

  refl-htpy-retract : (R : A retract-of B) → htpy-retract R R
  refl-htpy-retract R = (refl-htpy , refl-htpy , refl-htpy)

  htpy-eq-retract : (R S : A retract-of B) → R ＝ S → htpy-retract R S
  htpy-eq-retract R .R refl = refl-htpy-retract R

  is-torsorial-htpy-retract :
    (R : A retract-of B) → is-torsorial (htpy-retract R)
  is-torsorial-htpy-retract R =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (inclusion-retract R))
      ( inclusion-retract R , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-retraction-retract R))
        ( map-retraction-retract R , refl-htpy)
        ( is-torsorial-htpy (is-retraction-map-retraction-retract R)))

  is-equiv-htpy-eq-retract :
    (R S : A retract-of B) → is-equiv (htpy-eq-retract R S)
  is-equiv-htpy-eq-retract R =
    fundamental-theorem-id (is-torsorial-htpy-retract R) (htpy-eq-retract R)

  equiv-htpy-eq-retract : (R S : A retract-of B) → (R ＝ S) ≃ htpy-retract R S
  equiv-htpy-eq-retract R S =
    ( htpy-eq-retract R S , is-equiv-htpy-eq-retract R S)

  eq-htpy-retract : (R S : A retract-of B) → htpy-retract R S → R ＝ S
  eq-htpy-retract R S = map-inv-is-equiv (is-equiv-htpy-eq-retract R S)
```

## See also

- [Retracts of maps](foundation.retracts-of-maps.md)
