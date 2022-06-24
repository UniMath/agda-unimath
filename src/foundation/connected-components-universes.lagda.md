# Connected components of universes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.connected-components-universes where

open import foundation.connected-types using
  ( is-path-connected; is-path-connected-mere-eq)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( empty; equiv-is-empty; empty-Prop; raise-empty)
open import foundation.equivalences using
  ( _≃_; id-equiv; is-equiv; map-inv-is-equiv; map-inv-equiv)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; refl)
open import foundation.mere-equivalences using
  ( mere-equiv-Prop; mere-equiv; is-prop-mere-equiv; refl-mere-equiv)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.raising-universe-levels using (equiv-raise)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.subtypes using (type-subtype)
open import foundation.subuniverses using (eq-equiv-subuniverse)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_; lzero)
```

## Idea

The connected component of a universe `UU l` at a type `A : UU l` is the type of all `X : UU l` that are merely equivalent to `A`. More generally, we define the component of a universe `UU l1` of types merely equal to `A : UU l2`.

## Definition

### The connected component of a universe with variable universe.

```agda
component-UU-Level :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
component-UU-Level l1 A = type-subtype (mere-equiv-Prop {l2 = l1} A)

type-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} → component-UU-Level l1 A → UU l1
type-component-UU-Level X = pr1 X

abstract
  mere-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    mere-equiv A (type-component-UU-Level X)
  mere-equiv-component-UU-Level X = pr2 X
```

### The connected component of a universe

```agda
component-UU :
  {l1 : Level} (A : UU l1) → UU (lsuc l1)
component-UU {l1} A = component-UU-Level l1 A

type-component-UU : {l1 : Level} {A : UU l1} (X : component-UU A) → UU l1
type-component-UU X = type-component-UU-Level X

abstract
  mere-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    mere-equiv A (type-component-UU X)
  mere-equiv-component-UU X = mere-equiv-component-UU-Level X
```

## Properties

### Characterization of the identity types of `component-UU`

```agda
equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) → UU l1
equiv-component-UU-Level X Y =
  type-component-UU-Level X ≃ type-component-UU-Level Y

id-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  equiv-component-UU-Level X X
id-equiv-component-UU-Level X = id-equiv

equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} {X Y : component-UU-Level l1 A} →
  Id X Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

abstract
  is-contr-total-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    is-contr (Σ (component-UU-Level l1 A) (equiv-component-UU-Level X))
  is-contr-total-equiv-component-UU-Level X =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv (type-component-UU-Level X))
      ( λ Y → is-prop-mere-equiv _ Y)
      ( type-component-UU-Level X)
      ( id-equiv)
      ( mere-equiv-component-UU-Level X)

abstract
  is-equiv-equiv-eq-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
    is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
  is-equiv-equiv-eq-component-UU-Level X =
    fundamental-theorem-id X
      ( id-equiv-component-UU-Level X)
      ( is-contr-total-equiv-component-UU-Level X)
      ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → Id X Y
eq-equiv-component-UU-Level X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-component-UU-Level X Y)

equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) → UU l1
equiv-component-UU X Y = equiv-component-UU-Level X Y

id-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) → equiv-component-UU X X
id-equiv-component-UU X = id-equiv-component-UU-Level X

equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} {X Y : component-UU A} →
  Id X Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

abstract
  is-contr-total-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    is-contr (Σ (component-UU A) (equiv-component-UU X))
  is-contr-total-equiv-component-UU X =
    is-contr-total-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-component-UU :
    {l1 : Level} {A : UU l1} (X Y : component-UU A) →
    is-equiv (equiv-eq-component-UU {X = X} {Y})
  is-equiv-equiv-eq-component-UU X Y =
    is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → Id X Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y
```

```agda
abstract
  is-contr-component-UU-Level-empty :
    (l : Level) → is-contr (component-UU-Level l empty)
  pr1 (pr1 (is-contr-component-UU-Level-empty l)) = raise-empty l
  pr2 (pr1 (is-contr-component-UU-Level-empty l)) =
    unit-trunc-Prop (equiv-raise l empty)
  pr2 (is-contr-component-UU-Level-empty l) X =
    eq-equiv-subuniverse
      ( mere-equiv-Prop empty)
      ( equiv-is-empty
        ( map-inv-equiv (equiv-raise l empty))
        ( λ x →
          apply-universal-property-trunc-Prop
          ( pr2 X)
          ( empty-Prop)
          ( λ e → map-inv-equiv e x)))

abstract
  is-contr-component-UU-empty : is-contr (component-UU empty)
  is-contr-component-UU-empty =
    is-contr-component-UU-Level-empty lzero
```

### The connected components of universes are path connected

```agda
abstract
  is-path-connected-component-UU :
    {l : Level} (X : UU l) → is-path-connected (component-UU X)
  is-path-connected-component-UU X =
    is-path-connected-mere-eq
      ( pair X (refl-mere-equiv X))
      ( λ Y →
        map-trunc-Prop
          ( eq-equiv-component-UU (pair X (refl-mere-equiv X)) Y)
          ( mere-equiv-component-UU Y))
```
