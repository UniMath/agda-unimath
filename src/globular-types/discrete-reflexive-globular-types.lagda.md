# Discrete reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.discrete-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.reflexive-globular-types
open import globular-types.symmetric-globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

A [reflexive globular type](globular-types.reflexive-globular-types.md) is said
to be
{{#concept "discrete" Disambiguation="reflexive globular type" Agda=is-discrete-Reflexive-Globular-Type}}
if:

- For every 0-cell `x` the type family `G₁ x` of 1-cells out of `x` is
  [torsorial](foundation-core.torsorial-type-families.md), and
- For every two 0-cells `x` and `y` the reflexive globular type `G' x y` is
  discrete.

The {{#concept "standard discrete globular type"}} at a type `A` is the
[globular type](globular-types.globular-types.md) obtained from the iterated
[identity types](foundation-core.identity-types.md) on `A`. This globular type
is [reflexive](globular-types.reflexive-globular-types.md),
[transitive](globular-types.transitive-globular-types.md), and indeed
[discrete](globular-types.discrete-reflexive-globular-types.md).

## Definitions

### The predicate of being a discrete reflexive globular type

```agda
record
  is-discrete-Reflexive-Globular-Type
    {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type :
      (x : 0-cell-Reflexive-Globular-Type G) →
      is-torsorial (1-cell-Reflexive-Globular-Type G x)

  field
    is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type :
      (x y : 0-cell-Reflexive-Globular-Type G) →
      is-discrete-Reflexive-Globular-Type
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)

open is-discrete-Reflexive-Globular-Type public
```

### Discrete reflexive globular types

```agda
record
  Discrete-Reflexive-Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  eta-equality

  field
    reflexive-globular-type-Discrete-Reflexive-Globular-Type :
      Reflexive-Globular-Type l1 l2

  field
    is-discrete-Discrete-Reflexive-Globular-Type :
      is-discrete-Reflexive-Globular-Type
        reflexive-globular-type-Discrete-Reflexive-Globular-Type

open Discrete-Reflexive-Globular-Type public
```

### The standard discrete reflexive globular types

```agda
module _
  {l : Level}
  where

  globular-type-discrete-Reflexive-Globular-Type : UU l → Globular-Type l l
  0-cell-Globular-Type (globular-type-discrete-Reflexive-Globular-Type A) =
    A
  1-cell-globular-type-Globular-Type
    ( globular-type-discrete-Reflexive-Globular-Type A)
    ( x)
    ( y) =
    globular-type-discrete-Reflexive-Globular-Type (x ＝ y)

  refl-discrete-Reflexive-Globular-Type :
    {A : UU l} →
    is-reflexive-Globular-Type
      ( globular-type-discrete-Reflexive-Globular-Type A)
  is-reflexive-1-cell-is-reflexive-Globular-Type
    refl-discrete-Reflexive-Globular-Type
    x =
    refl
  is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
    refl-discrete-Reflexive-Globular-Type =
    refl-discrete-Reflexive-Globular-Type

  discrete-Reflexive-Globular-Type :
    (A : UU l) → Reflexive-Globular-Type l l
  globular-type-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A) =
    globular-type-discrete-Reflexive-Globular-Type A
  refl-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A) =
    refl-discrete-Reflexive-Globular-Type

  is-discrete-standard-Discrete-Reflexive-Globular-Type :
    {A : UU l} →
    is-discrete-Reflexive-Globular-Type (discrete-Reflexive-Globular-Type A)
  is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type
    is-discrete-standard-Discrete-Reflexive-Globular-Type
    x =
    is-torsorial-Id x
  is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type
    is-discrete-standard-Discrete-Reflexive-Globular-Type x y =
    is-discrete-standard-Discrete-Reflexive-Globular-Type

  standard-Discrete-Reflexive-Globular-Type :
    UU l → Discrete-Reflexive-Globular-Type l l
  reflexive-globular-type-Discrete-Reflexive-Globular-Type
    ( standard-Discrete-Reflexive-Globular-Type A) =
    discrete-Reflexive-Globular-Type A
  is-discrete-Discrete-Reflexive-Globular-Type
    ( standard-Discrete-Reflexive-Globular-Type A) =
    is-discrete-standard-Discrete-Reflexive-Globular-Type
```

## Properties

### The standard discrete reflexive globular types are transitive

```agda
is-transitive-discrete-Reflexive-Globular-Type :
  {l : Level} {A : UU l} →
  is-transitive-Globular-Type (globular-type-discrete-Reflexive-Globular-Type A)
comp-1-cell-is-transitive-Globular-Type
  is-transitive-discrete-Reflexive-Globular-Type q p =
  p ∙ q
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  is-transitive-discrete-Reflexive-Globular-Type =
  is-transitive-discrete-Reflexive-Globular-Type

discrete-Transitive-Globular-Type :
  {l : Level} (A : UU l) → Transitive-Globular-Type l l
globular-type-Transitive-Globular-Type (discrete-Transitive-Globular-Type A) =
  globular-type-discrete-Reflexive-Globular-Type A
is-transitive-Transitive-Globular-Type (discrete-Transitive-Globular-Type A) =
  is-transitive-discrete-Reflexive-Globular-Type
```

### The standard discrete reflexive globular types are symmetric

```agda
is-symmetric-discrete-Reflexive-Globular-Type :
  {l : Level} {A : UU l} →
  is-symmetric-Globular-Type (globular-type-discrete-Reflexive-Globular-Type A)
is-symmetric-1-cell-is-symmetric-Globular-Type
  is-symmetric-discrete-Reflexive-Globular-Type a b =
  inv
is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type
  is-symmetric-discrete-Reflexive-Globular-Type x y =
  is-symmetric-discrete-Reflexive-Globular-Type
```

## See also

- [Discrete dependent reflexive globular types](globular-types.discrete-dependent-reflexive-globular-types.md)
- [Discrete globular types](globular-types.discrete-globular-types.md)
- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
