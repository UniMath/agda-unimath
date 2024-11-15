# The standard discrete globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.standard-discrete-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.discrete-globular-types
open import structured-types.globular-types
open import structured-types.reflexive-globular-types
open import structured-types.symmetric-globular-types
open import structured-types.transitive-globular-types
```

</details>

## Idea

The {{#concept "standard discrete globular type"}} at a type `A` is the
[globular type](structured-types.globular-types.md) obtained from the iterated
[identity types](foundation-core.identity-types.md) on `A`. This globular type
is [reflexive](structured-types.reflexive-globular-types.md),
[transitive](structured-types.transitive-globular-types.md), and indeed
[discrete](structured-types.discrete-globular-types.md).

## Definitions

### The standard discrete globular types

```agda
module _
  {l : Level}
  where

  discrete-Globular-Type : UU l → Globular-Type l l
  0-cell-Globular-Type (discrete-Globular-Type A) =
    A
  1-cell-globular-type-Globular-Type ( discrete-Globular-Type A) x y =
    discrete-Globular-Type (x ＝ y)

  refl-discrete-Globular-Type :
    {A : UU l} → is-reflexive-Globular-Type (discrete-Globular-Type A)
  is-reflexive-1-cell-is-reflexive-Globular-Type refl-discrete-Globular-Type x =
    refl
  is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
    refl-discrete-Globular-Type =
    refl-discrete-Globular-Type

  discrete-Reflexive-Globular-Type :
    (A : UU l) → Reflexive-Globular-Type l l
  globular-type-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A) =
    discrete-Globular-Type A
  refl-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A) =
    refl-discrete-Globular-Type

  is-discrete-standard-Discrete-Globular-Type :
    {A : UU l} →
    is-discrete-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A)
  is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type
    is-discrete-standard-Discrete-Globular-Type x =
    is-torsorial-Id x
  is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type
    is-discrete-standard-Discrete-Globular-Type x y =
    is-discrete-standard-Discrete-Globular-Type

  standard-Discrete-Globular-Type :
    UU l → Discrete-Globular-Type l l
  reflexive-globular-type-Discrete-Globular-Type
    ( standard-Discrete-Globular-Type A) =
    discrete-Reflexive-Globular-Type A
  is-discrete-Discrete-Globular-Type
    ( standard-Discrete-Globular-Type A) =
    is-discrete-standard-Discrete-Globular-Type
```

## Properties

### The standard discrete globular types are transitive

```agda
is-transitive-discrete-Globular-Type :
  {l : Level} {A : UU l} →
  is-transitive-Globular-Type (discrete-Globular-Type A)
comp-1-cell-is-transitive-Globular-Type
  is-transitive-discrete-Globular-Type q p =
  p ∙ q
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  is-transitive-discrete-Globular-Type =
  is-transitive-discrete-Globular-Type

discrete-Transitive-Globular-Type :
  {l : Level} (A : UU l) → Transitive-Globular-Type l l
globular-type-Transitive-Globular-Type (discrete-Transitive-Globular-Type A) =
  discrete-Globular-Type A
is-transitive-Transitive-Globular-Type (discrete-Transitive-Globular-Type A) =
  is-transitive-discrete-Globular-Type
```

### The standard discrete globular types are symmetric

```agda
is-symmetric-discrete-Globular-Type :
  {l : Level} {A : UU l} →
  is-symmetric-Globular-Type (discrete-Globular-Type A)
is-symmetric-1-cell-is-symmetric-Globular-Type
  is-symmetric-discrete-Globular-Type a b =
  inv
is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type
  is-symmetric-discrete-Globular-Type x y =
  is-symmetric-discrete-Globular-Type
```
