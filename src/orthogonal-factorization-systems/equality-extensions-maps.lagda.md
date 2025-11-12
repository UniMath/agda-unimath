# Equality of extensions of maps

```agda
module orthogonal-factorization-systems.equality-extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.torsorial-type-families

open import orthogonal-factorization-systems.equality-extensions-dependent-maps
open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

We characterize equality of
[extensions](orthogonal-factorization-systems.extensions-maps.md) of maps.

## Definition

### Homotopies of extensions of maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} (f : A → X)
  where

  coherence-htpy-extension-map :
    (e e' : extension-map i f) →
    map-extension-map e ~ map-extension-map e' →
    UU (l1 ⊔ l3)
  coherence-htpy-extension-map =
    coherence-htpy-extension-dependent-map i f

  htpy-extension-map :
    (e e' : extension-map i f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension-map =
    htpy-extension-dependent-map i f

  refl-htpy-extension-map :
    (e : extension-map i f) → htpy-extension-map e e
  refl-htpy-extension-map =
    refl-htpy-extension-dependent-map i f
```

## Properties

### Homotopies characterize equality

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} (f : A → X)
  where

  htpy-eq-extension-map :
    (e e' : extension-map i f) → e ＝ e' → htpy-extension-map i f e e'
  htpy-eq-extension-map = htpy-eq-extension-dependent-map i f

  is-torsorial-htpy-extension-map :
    (e : extension-map i f) → is-torsorial (htpy-extension-map i f e)
  is-torsorial-htpy-extension-map =
    is-torsorial-htpy-extension-dependent-map i f

  is-equiv-htpy-eq-extension-map :
    (e e' : extension-map i f) → is-equiv (htpy-eq-extension-map e e')
  is-equiv-htpy-eq-extension-map =
    is-equiv-htpy-eq-extension-dependent-map i f

  extensionality-extension-map :
    (e e' : extension-map i f) → (e ＝ e') ≃ htpy-extension-map i f e e'
  extensionality-extension-map =
    extensionality-extension-dependent-map i f

  eq-htpy-extension-map :
    (e e' : extension-map i f) → htpy-extension-map i f e e' → e ＝ e'
  eq-htpy-extension-map =
    eq-htpy-extension-dependent-map i f
```
