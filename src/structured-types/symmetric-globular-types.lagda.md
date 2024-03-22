# Symmetric globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.symmetric-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

We say a [globular type](structured-types.globular-types.md) is
{{#concept "symmetric" Disambiguation="globular type" Agda=is-symmetric-globular-structure}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definition

### Symmetry structure on a globular structure

```agda
record
  is-symmetric-globular-structure
  {l : Level} {A : UU l} (G : globular-structure A) : UU l
  where
  coinductive
  field
    is-symmetric-1-cell-is-symmetric-globular-structure :
      is-symmetric (1-cell-globular-structure G)
    is-symmetric-globular-structure-1-cell-is-symmetric-globular-structure :
      (x y : A) →
      is-symmetric-globular-structure
        ( globular-structure-1-cell-globular-structure G x y)

open is-symmetric-globular-structure public

module _
  {l : Level} {A : UU l} {G : globular-structure A}
  (r : is-symmetric-globular-structure G)
  where

  sym-1-cell-is-symmetric-globular-structure :
    {x y : A} →
    1-cell-globular-structure G x y → 1-cell-globular-structure G y x
  sym-1-cell-is-symmetric-globular-structure {x} {y} =
    is-symmetric-1-cell-is-symmetric-globular-structure r x y

  sym-2-cell-is-symmetric-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    2-cell-globular-structure G f g →
    2-cell-globular-structure G g f
  sym-2-cell-is-symmetric-globular-structure {x} {y} {f} {g} =
    is-symmetric-1-cell-is-symmetric-globular-structure
      ( is-symmetric-globular-structure-1-cell-is-symmetric-globular-structure
        ( r)
        ( x)
        ( y))
      ( f)
      ( g)
```

### The type of symmetric globular structures

```agda
symmetric-globular-structure : {l : Level} (A : UU l) → UU (lsuc l)
symmetric-globular-structure A =
  Σ (globular-structure A) (is-symmetric-globular-structure)
```

## Examples

### The symmetric globular structure on a type given by its identity types

```agda
is-symmetric-globular-structure-Id :
  {l : Level} (A : UU l) →
  is-symmetric-globular-structure (globular-structure-Id A)
is-symmetric-globular-structure-Id A =
  λ where
  .is-symmetric-1-cell-is-symmetric-globular-structure x y →
    inv
  .is-symmetric-globular-structure-1-cell-is-symmetric-globular-structure x y →
    is-symmetric-globular-structure-Id (x ＝ y)
```
