# Connected components of universes

```agda
open import foundation.function-extensionality-axiom

module
  foundation.connected-components-universes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext
open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.functoriality-propositional-truncation funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.mere-equivalences funext
open import foundation.propositional-truncations funext
open import foundation.raising-universe-levels funext
open import foundation.subtype-identity-principle
open import foundation.subuniverses funext
open import foundation.univalence funext
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.subtypes funext
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The **connected component** of a universe `UU l` at a type `A : UU l` is the
type of all `X : UU l` that are
[merely equivalent](foundation.mere-equivalences.md) to `A`. More generally, we
define the component of a universe `UU l1` of types
[merely equal](foundation.mere-equality.md) to `A : UU l2`.

## Definition

### The connected component of a universe with variable universe

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
  X ＝ Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

abstract
  is-torsorial-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    is-torsorial (equiv-component-UU-Level X)
  is-torsorial-equiv-component-UU-Level X =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv (type-component-UU-Level X))
      ( λ Y → is-prop-mere-equiv _ Y)
      ( type-component-UU-Level X)
      ( id-equiv)
      ( mere-equiv-component-UU-Level X)

abstract
  is-equiv-equiv-eq-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
    is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
  is-equiv-equiv-eq-component-UU-Level X =
    fundamental-theorem-id
      ( is-torsorial-equiv-component-UU-Level X)
      ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → X ＝ Y
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
  X ＝ Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

abstract
  is-torsorial-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    is-torsorial (equiv-component-UU X)
  is-torsorial-equiv-component-UU X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-component-UU :
    {l1 : Level} {A : UU l1} (X Y : component-UU A) →
    is-equiv (equiv-eq-component-UU {X = X} {Y})
  is-equiv-equiv-eq-component-UU X Y =
    is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → X ＝ Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y
```

```agda
abstract
  is-contr-component-UU-Level-empty :
    (l : Level) → is-contr (component-UU-Level l empty)
  pr1 (pr1 (is-contr-component-UU-Level-empty l)) = raise-empty l
  pr2 (pr1 (is-contr-component-UU-Level-empty l)) =
    unit-trunc-Prop (compute-raise l empty)
  pr2 (is-contr-component-UU-Level-empty l) X =
    eq-equiv-subuniverse
      ( mere-equiv-Prop empty)
      ( equiv-is-empty
        ( map-inv-equiv (compute-raise l empty))
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

### The connected components of universes are `0`-connected

```agda
abstract
  is-0-connected-component-UU :
    {l : Level} (X : UU l) → is-0-connected (component-UU X)
  is-0-connected-component-UU X =
    is-0-connected-mere-eq
      ( pair X (refl-mere-equiv X))
      ( λ Y →
        map-trunc-Prop
          ( eq-equiv-component-UU (pair X (refl-mere-equiv X)) Y)
          ( mere-equiv-component-UU Y))
```
