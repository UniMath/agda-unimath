# Symmetric globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.symmetric-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-types
```

</details>

## Idea

We say a [globular type](globular-types.globular-types.md) is
{{#concept "symmetric" Disambiguation="globular type" Agda=is-symmetric-Globular-Type}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definition

### Symmetry structure on a globular type

```agda
record
  is-symmetric-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    is-symmetric-1-cell-is-symmetric-Globular-Type :
      is-symmetric (1-cell-Globular-Type G)

  field
    is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type :
      (x y : 0-cell-Globular-Type G) →
      is-symmetric-Globular-Type (1-cell-globular-type-Globular-Type G x y)

open is-symmetric-Globular-Type public
```

### Symmetric globular types

```agda
record
  Symmetric-Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  field
    globular-type-Symmetric-Globular-Type : Globular-Type l1 l2

  0-cell-Symmetric-Globular-Type : UU l1
  0-cell-Symmetric-Globular-Type =
    0-cell-Globular-Type globular-type-Symmetric-Globular-Type

  1-cell-globular-type-Symmetric-Globular-Type :
    (x y : 0-cell-Symmetric-Globular-Type) →
    Globular-Type l2 l2
  1-cell-globular-type-Symmetric-Globular-Type =
    1-cell-globular-type-Globular-Type globular-type-Symmetric-Globular-Type

  1-cell-Symmetric-Globular-Type :
    (x y : 0-cell-Symmetric-Globular-Type) → UU l2
  1-cell-Symmetric-Globular-Type =
    1-cell-Globular-Type globular-type-Symmetric-Globular-Type

  field
    is-symmetric-Symmetric-Globular-Type :
      is-symmetric-Globular-Type globular-type-Symmetric-Globular-Type

  inv-1-cell-Symmetric-Globular-Type :
    {x y : 0-cell-Symmetric-Globular-Type} →
    1-cell-Symmetric-Globular-Type x y → 1-cell-Symmetric-Globular-Type y x
  inv-1-cell-Symmetric-Globular-Type =
    is-symmetric-1-cell-is-symmetric-Globular-Type
      is-symmetric-Symmetric-Globular-Type
      _
      _

  is-symmetric-1-cell-globular-type-Symmetric-Globular-Type :
    (x y : 0-cell-Symmetric-Globular-Type) →
    is-symmetric-Globular-Type
      ( 1-cell-globular-type-Symmetric-Globular-Type x y)
  is-symmetric-1-cell-globular-type-Symmetric-Globular-Type =
    is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type
      is-symmetric-Symmetric-Globular-Type

  1-cell-symmetric-globular-type-Symmetric-Globular-Type :
    (x y : 0-cell-Symmetric-Globular-Type) →
    Symmetric-Globular-Type l2 l2
  globular-type-Symmetric-Globular-Type
    ( 1-cell-symmetric-globular-type-Symmetric-Globular-Type x y) =
    1-cell-globular-type-Symmetric-Globular-Type x y
  is-symmetric-Symmetric-Globular-Type
    ( 1-cell-symmetric-globular-type-Symmetric-Globular-Type x y) =
    is-symmetric-1-cell-globular-type-Symmetric-Globular-Type x y

open Symmetric-Globular-Type public
```
