# Discrete globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.discrete-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.reflexive-globular-types
```

</details>

## Idea

A [reflexive globular type](structured-types.reflexive-globular-types.md) is
said to be
{{#concept "discrete" Disambiguation="reflexive globular type" Agda=is-discrete-Reflexive-Globular-Type}}
if:

- For every 0-cell `x` the type family `G₁ x` of 1-cells out of `x` is
  [torsorial](foundation-core.torsorial-type-families.md), and
- For every two 0-cells `x` and `y` the reflexive globular type `G' x y` is
  discrete.

## Definitions

### The predicate of being a discrete globular type

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

### Discrete globular types

```agda
record
  Discrete-Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  field
    reflexive-globular-type-Discrete-Globular-Type :
      Reflexive-Globular-Type l1 l2

  field
    is-discrete-Discrete-Globular-Type :
      is-discrete-Reflexive-Globular-Type
        reflexive-globular-type-Discrete-Globular-Type

open Discrete-Globular-Type public
```
