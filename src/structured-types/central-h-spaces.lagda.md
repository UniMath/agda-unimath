# Central H-spaces

```agda
module structured-types.central-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import structured-types.connected-h-spaces
open import structured-types.h-spaces
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

In [`structured-types.h-spaces`](structured-types.h-spaces.md) we saw that the
type of H-space structures on a
[pointed type](structured-types.pointed-types.md) `A` is equivalently described
as the type of [pointed sections](structured-types.pointed-types.md) of the
pointed evaluation map `(A → A) →∗ A`. If the type `A` is
[0-connected](foundation.0-connected-types.md), then the section maps to the
[connected component](foundation.connected-components.md) of `(A ≃ A)` at the
identity [equivalence](foundation-core.equivalences.md). Now the question arises
for which H-spaces this evaluation map `(A → A) →∗ A` is an equivalence. This
leads to the concept of _central H-space_.

A {{#concept "central pointed type" agda=Central-Pointed-Type}} is a
[pointed type](structured-types.pointed-types.md) such that the map
`ev_pt : (A → A)_{(id)} → A` from the connected component of the identity
function is an equivalence. Note that every type of endofunctions is an H-space.

## Definitions

### The predicate of being a central pointed type

```agda
is-central-Pointed-Type :
  {l : Level} (A : Pointed-Type l) → UU l
is-central-Pointed-Type A =
  is-equiv
    { A = connected-component (type-Pointed-Type A → type-Pointed-Type A) id}
    ( ev-point-Pointed-Type A ∘ pr1)
```

### Central pointed types

```agda
Central-Pointed-Type : (l : Level) → UU (lsuc l)
Central-Pointed-Type l = Σ (Pointed-Type l) is-central-Pointed-Type

module _
  {l : Level} (A : Central-Pointed-Type l)
  where

  pointed-type-Central-Pointed-Type : Pointed-Type l
  pointed-type-Central-Pointed-Type = pr1 A

  type-Central-Pointed-Type : UU l
  type-Central-Pointed-Type =
    type-Pointed-Type pointed-type-Central-Pointed-Type

  point-Central-Pointed-Type : type-Central-Pointed-Type
  point-Central-Pointed-Type =
    point-Pointed-Type pointed-type-Central-Pointed-Type

  is-central-Central-Pointed-Type :
    is-central-Pointed-Type pointed-type-Central-Pointed-Type
  is-central-Central-Pointed-Type = pr2 A

  ev-point-Central-Pointed-Type :
    connected-component
      ( type-Central-Pointed-Type → type-Central-Pointed-Type)
      ( id) →
    type-Central-Pointed-Type
  ev-point-Central-Pointed-Type =
    ev-point-Pointed-Type pointed-type-Central-Pointed-Type ∘ pr1

  ev-point-equiv-Central-Pointed-Type :
    connected-component
      ( type-Central-Pointed-Type → type-Central-Pointed-Type)
      ( id) ≃
    type-Central-Pointed-Type
  pr1 ev-point-equiv-Central-Pointed-Type = ev-point-Central-Pointed-Type
  pr2 ev-point-equiv-Central-Pointed-Type = is-central-Central-Pointed-Type
```

### The predicate of being a central H-space

```agda
module _
  {l : Level} (A : H-Space l)
  where

  is-central-H-Space : UU l
  is-central-H-Space =
    is-0-connected-H-Space A ×
    is-set (pointed-type-H-Space A →∗ pointed-type-H-Space A)

  is-0-connected-is-central-H-Space :
    is-central-H-Space → is-0-connected-H-Space A
  is-0-connected-is-central-H-Space = pr1

  is-set-pointed-endomap-is-central-H-Space :
    is-central-H-Space →
    is-set (pointed-type-H-Space A →∗ pointed-type-H-Space A)
  is-set-pointed-endomap-is-central-H-Space = pr2
```

### Central H-spaces

```agda
Central-H-Space :
  (l : Level) → UU (lsuc l)
Central-H-Space l = Σ (H-Space l) is-central-H-Space

module _
  {l : Level} (A : Central-H-Space l)
  where

  h-space-Central-H-Space : H-Space l
  h-space-Central-H-Space = pr1 A

  pointed-type-Central-H-Space : Pointed-Type l
  pointed-type-Central-H-Space =
    pointed-type-H-Space h-space-Central-H-Space

  type-Central-H-Space : UU l
  type-Central-H-Space = type-H-Space h-space-Central-H-Space

  unit-Central-H-Space : type-Central-H-Space
  unit-Central-H-Space = unit-H-Space h-space-Central-H-Space

  mul-Central-H-Space :
    (x y : type-Central-H-Space) → type-Central-H-Space
  mul-Central-H-Space = mul-H-Space h-space-Central-H-Space

  left-unit-law-mul-Central-H-Space :
    (x : type-Central-H-Space) →
    mul-Central-H-Space unit-Central-H-Space x ＝ x
  left-unit-law-mul-Central-H-Space =
    left-unit-law-mul-H-Space h-space-Central-H-Space

  right-unit-law-mul-Central-H-Space :
    (x : type-Central-H-Space) →
    mul-Central-H-Space x unit-Central-H-Space ＝ x
  right-unit-law-mul-Central-H-Space =
    right-unit-law-mul-H-Space h-space-Central-H-Space

  coh-unit-laws-mul-Central-H-Space :
    left-unit-law-mul-Central-H-Space unit-Central-H-Space ＝
    right-unit-law-mul-Central-H-Space unit-Central-H-Space
  coh-unit-laws-mul-Central-H-Space =
    coh-unit-laws-mul-H-Space h-space-Central-H-Space

  is-central-Central-H-Space :
    is-central-H-Space h-space-Central-H-Space
  is-central-Central-H-Space = pr2 A

  is-0-connected-Central-H-Space :
    is-0-connected-H-Space h-space-Central-H-Space
  is-0-connected-Central-H-Space =
    is-0-connected-is-central-H-Space
      ( h-space-Central-H-Space)
      ( is-central-Central-H-Space)

  is-set-pointed-endomap-Central-H-Space :
    is-set (pointed-type-Central-H-Space →∗ pointed-type-Central-H-Space)
  is-set-pointed-endomap-Central-H-Space =
    is-set-pointed-endomap-is-central-H-Space
      ( h-space-Central-H-Space)
      ( is-central-Central-H-Space)
```

## Properties

### Central pointed types are connected

```agda
module _
  {l1 : Level} (A : Central-Pointed-Type l1)
  where

  is-0-connected-Central-Pointed-Type :
    is-0-connected (type-Central-Pointed-Type A)
  is-0-connected-Central-Pointed-Type =
    is-0-connected-equiv'
      ( ev-point-equiv-Central-Pointed-Type A)
      ( is-0-connected-connected-component
        ( type-Central-Pointed-Type A → type-Central-Pointed-Type A)
        ( id))
```

### Central pointed types are central H-Spaces

## References

{{#bibliography}} {{#reference BCFR23}}
