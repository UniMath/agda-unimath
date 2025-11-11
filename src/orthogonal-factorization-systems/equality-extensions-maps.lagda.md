# Equality of extensions of maps

```agda
module orthogonal-factorization-systems.equality-extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.torsorial-type-families

open import orthogonal-factorization-systems.extensions-dependent-maps
```

</details>

## Idea

We characterize equality of
[extensions](orthogonal-factorization-systems.extensions-maps.md) of
([dependent](orthogonal-factorization-systems.extensions-dependent-maps.md))
maps.

## Definition

### Homotopies of extensions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  coherence-htpy-extension :
    (e e' : extension-dependent-type i P f) →
    map-extension-dependent-type e ~ map-extension-dependent-type e' →
    UU (l1 ⊔ l3)
  coherence-htpy-extension e e' K =
    ( is-extension-map-extension-dependent-type e ∙h (K ·r i)) ~
    ( is-extension-map-extension-dependent-type e')

  htpy-extension : (e e' : extension-dependent-type i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension e e' =
    Σ ( map-extension-dependent-type e ~ map-extension-dependent-type e')
      ( coherence-htpy-extension e e')

  refl-htpy-extension :
    (e : extension-dependent-type i P f) → htpy-extension e e
  pr1 (refl-htpy-extension e) = refl-htpy
  pr2 (refl-htpy-extension e) = right-unit-htpy
```

### Homotopies of extensions with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  coherence-htpy-extension' :
    (e e' : extension-dependent-type' i P f) →
    map-extension-dependent-type' e ~ map-extension-dependent-type' e' →
    UU (l1 ⊔ l3)
  coherence-htpy-extension' e e' K =
    ( is-extension-map-extension-dependent-type' e) ~
    ( K ·r i ∙h is-extension-map-extension-dependent-type' e')

  htpy-extension' :
    (e e' : extension-dependent-type' i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension' e e' =
    Σ ( map-extension-dependent-type' e ~ map-extension-dependent-type' e')
      ( coherence-htpy-extension' e e')

  refl-htpy-extension' :
    (e : extension-dependent-type' i P f) → htpy-extension' e e
  pr1 (refl-htpy-extension' e) = refl-htpy
  pr2 (refl-htpy-extension' e) = refl-htpy
```

## Properties

### Homotopies characterize equality

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  htpy-eq-extension :
    (e e' : extension-dependent-type i P f) → e ＝ e' → htpy-extension i f e e'
  htpy-eq-extension e .e refl = refl-htpy-extension i f e

  abstract
    is-torsorial-htpy-extension :
      (e : extension-dependent-type i P f) → is-torsorial (htpy-extension i f e)
    is-torsorial-htpy-extension e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-extension-dependent-type e))
        ( map-extension-dependent-type e , refl-htpy)
        ( is-torsorial-htpy
          ( is-extension-map-extension-dependent-type e ∙h
            refl-htpy))

  abstract
    is-equiv-htpy-eq-extension :
      (e e' : extension-dependent-type i P f) →
      is-equiv (htpy-eq-extension e e')
    is-equiv-htpy-eq-extension e =
      fundamental-theorem-id
        ( is-torsorial-htpy-extension e)
        ( htpy-eq-extension e)

  extensionality-extension :
    (e e' : extension-dependent-type i P f) →
    (e ＝ e') ≃ htpy-extension i f e e'
  pr1 (extensionality-extension e e') = htpy-eq-extension e e'
  pr2 (extensionality-extension e e') = is-equiv-htpy-eq-extension e e'

  eq-htpy-extension :
    (e e' : extension-dependent-type i P f)
    (H : map-extension-dependent-type e ~ map-extension-dependent-type e') →
    coherence-htpy-extension i f e e' H → e ＝ e'
  eq-htpy-extension e e' H K =
    map-inv-equiv (extensionality-extension e e') (H , K)
```

### Characterizing equality of extensions of dependent maps with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  htpy-eq-extension' :
    (e e' : extension-dependent-type' i P f) →
    e ＝ e' → htpy-extension' i f e e'
  htpy-eq-extension' e .e refl =
    refl-htpy-extension' i f e

  abstract
    is-torsorial-htpy-extension' :
      (e : extension-dependent-type' i P f) →
      is-torsorial (htpy-extension' i f e)
    is-torsorial-htpy-extension' e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-extension-dependent-type' e))
        ( map-extension-dependent-type' e , refl-htpy)
        ( is-torsorial-htpy
          ( is-extension-map-extension-dependent-type' e))

  abstract
    is-equiv-htpy-eq-extension' :
      (e e' : extension-dependent-type' i P f) →
      is-equiv (htpy-eq-extension' e e')
    is-equiv-htpy-eq-extension' e =
      fundamental-theorem-id
        ( is-torsorial-htpy-extension' e)
        ( htpy-eq-extension' e)

  extensionality-extension' :
    (e e' : extension-dependent-type' i P f) →
    (e ＝ e') ≃ (htpy-extension' i f e e')
  pr1 (extensionality-extension' e e') =
    htpy-eq-extension' e e'
  pr2 (extensionality-extension' e e') =
    is-equiv-htpy-eq-extension' e e'

  eq-htpy-extension' :
    (e e' : extension-dependent-type' i P f) →
    htpy-extension' i f e e' → e ＝ e'
  eq-htpy-extension' e e' =
    map-inv-equiv (extensionality-extension' e e')
```
