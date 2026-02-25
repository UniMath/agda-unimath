# Equality of extensions of dependent maps

```agda
module orthogonal-factorization-systems.equality-extensions-dependent-maps where
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

open import orthogonal-factorization-systems.extensions-dependent-maps
```

</details>

## Idea

We characterize equality of
[extensions](orthogonal-factorization-systems.extensions-dependent-maps.md) of
dependent maps.

## Definition

### Homotopies of extensions of dependent maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  coherence-htpy-extension-dependent-map :
    (e e' : extension-dependent-map i P f) →
    map-extension-dependent-map e ~ map-extension-dependent-map e' →
    UU (l1 ⊔ l3)
  coherence-htpy-extension-dependent-map e e' K =
    ( is-extension-map-extension-dependent-map e ∙h (K ·r i)) ~
    ( is-extension-map-extension-dependent-map e')

  htpy-extension-dependent-map :
    (e e' : extension-dependent-map i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension-dependent-map e e' =
    Σ ( map-extension-dependent-map e ~ map-extension-dependent-map e')
      ( coherence-htpy-extension-dependent-map e e')

  refl-htpy-extension-dependent-map :
    (e : extension-dependent-map i P f) → htpy-extension-dependent-map e e
  pr1 (refl-htpy-extension-dependent-map e) = refl-htpy
  pr2 (refl-htpy-extension-dependent-map e) = right-unit-htpy
```

### Homotopies of extensions with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  coherence-htpy-extension-dependent-map' :
    (e e' : extension-dependent-map' i P f) →
    map-extension-dependent-map' e ~ map-extension-dependent-map' e' →
    UU (l1 ⊔ l3)
  coherence-htpy-extension-dependent-map' e e' K =
    ( is-extension-map-extension-dependent-map' e) ~
    ( K ·r i ∙h is-extension-map-extension-dependent-map' e')

  htpy-extension-dependent-map' :
    (e e' : extension-dependent-map' i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension-dependent-map' e e' =
    Σ ( map-extension-dependent-map' e ~ map-extension-dependent-map' e')
      ( coherence-htpy-extension-dependent-map' e e')

  refl-htpy-extension-dependent-map' :
    (e : extension-dependent-map' i P f) → htpy-extension-dependent-map' e e
  pr1 (refl-htpy-extension-dependent-map' e) = refl-htpy
  pr2 (refl-htpy-extension-dependent-map' e) = refl-htpy
```

## Properties

### Homotopies characterize equality

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  htpy-eq-extension-dependent-map :
    (e e' : extension-dependent-map i P f) →
    e ＝ e' → htpy-extension-dependent-map i f e e'
  htpy-eq-extension-dependent-map e .e refl =
    refl-htpy-extension-dependent-map i f e

  abstract
    is-torsorial-htpy-extension-dependent-map :
      (e : extension-dependent-map i P f) →
      is-torsorial (htpy-extension-dependent-map i f e)
    is-torsorial-htpy-extension-dependent-map e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-extension-dependent-map e))
        ( map-extension-dependent-map e , refl-htpy)
        ( is-torsorial-htpy
          ( is-extension-map-extension-dependent-map e ∙h
            refl-htpy))

  abstract
    is-equiv-htpy-eq-extension-dependent-map :
      (e e' : extension-dependent-map i P f) →
      is-equiv (htpy-eq-extension-dependent-map e e')
    is-equiv-htpy-eq-extension-dependent-map e =
      fundamental-theorem-id
        ( is-torsorial-htpy-extension-dependent-map e)
        ( htpy-eq-extension-dependent-map e)

  extensionality-extension-dependent-map :
    (e e' : extension-dependent-map i P f) →
    (e ＝ e') ≃ htpy-extension-dependent-map i f e e'
  pr1 (extensionality-extension-dependent-map e e') =
    htpy-eq-extension-dependent-map e e'
  pr2 (extensionality-extension-dependent-map e e') =
    is-equiv-htpy-eq-extension-dependent-map e e'

  eq-htpy-extension-dependent-map :
    (e e' : extension-dependent-map i P f) →
    htpy-extension-dependent-map i f e e' → e ＝ e'
  eq-htpy-extension-dependent-map e e' =
    map-inv-equiv (extensionality-extension-dependent-map e e')
```

### Characterizing equality of extensions of dependent maps with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (f : (x : A) → P (i x))
  where

  htpy-eq-extension-dependent-map' :
    (e e' : extension-dependent-map' i P f) →
    e ＝ e' → htpy-extension-dependent-map' i f e e'
  htpy-eq-extension-dependent-map' e .e refl =
    refl-htpy-extension-dependent-map' i f e

  abstract
    is-torsorial-htpy-extension-dependent-map' :
      (e : extension-dependent-map' i P f) →
      is-torsorial (htpy-extension-dependent-map' i f e)
    is-torsorial-htpy-extension-dependent-map' e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-extension-dependent-map' e))
        ( map-extension-dependent-map' e , refl-htpy)
        ( is-torsorial-htpy
          ( is-extension-map-extension-dependent-map' e))

  abstract
    is-equiv-htpy-eq-extension-dependent-map' :
      (e e' : extension-dependent-map' i P f) →
      is-equiv (htpy-eq-extension-dependent-map' e e')
    is-equiv-htpy-eq-extension-dependent-map' e =
      fundamental-theorem-id
        ( is-torsorial-htpy-extension-dependent-map' e)
        ( htpy-eq-extension-dependent-map' e)

  extensionality-extension-dependent-map' :
    (e e' : extension-dependent-map' i P f) →
    (e ＝ e') ≃ (htpy-extension-dependent-map' i f e e')
  pr1 (extensionality-extension-dependent-map' e e') =
    htpy-eq-extension-dependent-map' e e'
  pr2 (extensionality-extension-dependent-map' e e') =
    is-equiv-htpy-eq-extension-dependent-map' e e'

  eq-htpy-extension-dependent-map' :
    (e e' : extension-dependent-map' i P f) →
    htpy-extension-dependent-map' i f e e' → e ＝ e'
  eq-htpy-extension-dependent-map' e e' =
    map-inv-equiv (extensionality-extension-dependent-map' e e')
```
