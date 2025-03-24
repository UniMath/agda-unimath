# Large symmetric globular types

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module globular-types.large-symmetric-globular-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations funext univalence truncations
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.large-globular-types
open import globular-types.symmetric-globular-types funext univalence truncations
```

</details>

## Idea

We say that a [large globular type](globular-types.large-globular-types.md) is
{{#concept "symmetric" Disambiguation="large globular type" Agda=is-symmetric-Large-Globular-Type}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definitions

### Symmetry structure on a large globular type

```agda
record
  is-symmetric-Large-Globular-Type
    {α : Level → Level} {β : Level → Level → Level}
    (G : Large-Globular-Type α β) :
    UUω
  where

  field
    inv-1-cell-is-symmetric-Large-Globular-Type :
      is-symmetric-Large-Relation
        ( 0-cell-Large-Globular-Type G)
        ( 1-cell-Large-Globular-Type G)

  field
    is-symmetric-1-cell-globular-type-is-symmetric-Large-Globular-Type :
      {l1 l2 : Level}
      (x : 0-cell-Large-Globular-Type G l1) →
      (y : 0-cell-Large-Globular-Type G l2) →
      is-symmetric-Globular-Type
        ( 1-cell-globular-type-Large-Globular-Type G x y)

open is-symmetric-Large-Globular-Type public
```

### Large symmetric globular types

```agda
record
  Large-Symmetric-Globular-Type
    (α : Level → Level) (β : Level → Level → Level) :
    UUω
  where

  field
    large-globular-type-Large-Symmetric-Globular-Type :
      Large-Globular-Type α β

  0-cell-Large-Symmetric-Globular-Type :
    (l1 : Level) → UU (α l1)
  0-cell-Large-Symmetric-Globular-Type =
    0-cell-Large-Globular-Type large-globular-type-Large-Symmetric-Globular-Type

  1-cell-globular-type-Large-Symmetric-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Symmetric-Globular-Type l1)
    (y : 0-cell-Large-Symmetric-Globular-Type l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  1-cell-globular-type-Large-Symmetric-Globular-Type =
    1-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Symmetric-Globular-Type

  1-cell-Large-Symmetric-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Symmetric-Globular-Type l1)
    (y : 0-cell-Large-Symmetric-Globular-Type l2) →
    UU (β l1 l2)
  1-cell-Large-Symmetric-Globular-Type =
    1-cell-Large-Globular-Type large-globular-type-Large-Symmetric-Globular-Type

  field
    is-symmetric-Large-Symmetric-Globular-Type :
      is-symmetric-Large-Globular-Type
        large-globular-type-Large-Symmetric-Globular-Type

  inv-1-cell-Large-Symmetric-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Symmetric-Globular-Type l1}
    {y : 0-cell-Large-Symmetric-Globular-Type l2} →
    1-cell-Large-Symmetric-Globular-Type x y →
    1-cell-Large-Symmetric-Globular-Type y x
  inv-1-cell-Large-Symmetric-Globular-Type =
    inv-1-cell-is-symmetric-Large-Globular-Type
      is-symmetric-Large-Symmetric-Globular-Type
      _
      _

  is-symmetric-1-cell-globular-type-Large-Symmetric-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Symmetric-Globular-Type l1)
    (y : 0-cell-Large-Symmetric-Globular-Type l2) →
    is-symmetric-Globular-Type
      ( 1-cell-globular-type-Large-Symmetric-Globular-Type x y)
  is-symmetric-1-cell-globular-type-Large-Symmetric-Globular-Type =
    is-symmetric-1-cell-globular-type-is-symmetric-Large-Globular-Type
      is-symmetric-Large-Symmetric-Globular-Type

open Large-Symmetric-Globular-Type public
```
