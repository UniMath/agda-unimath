# Large symmetric globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-symmetric-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.universe-levels

open import structured-types.large-globular-types
open import structured-types.symmetric-globular-types
```

</details>

## Idea

We say a [large globular type](structured-types.large-globular-types.md) is
{{#concept "symmetric" Disambiguation="large globular type" Agda=is-symmetric-large-globular-structure}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definition

### Symmetry structure on a large globular structure

```agda
record
  is-symmetric-large-globular-structure
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A) : UUω
  where
  field
    is-symmetric-1-cell-is-symmetric-large-globular-structure :
      is-symmetric-Large-Relation A (1-cell-large-globular-structure G)
    is-symmetric-globular-structure-1-cell-is-symmetric-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      is-symmetric-globular-structure
        ( globular-structure-1-cell-large-globular-structure G x y)

open is-symmetric-large-globular-structure public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A)
  (r : is-symmetric-large-globular-structure G)
  where

  sym-1-cell-is-symmetric-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2} →
    1-cell-large-globular-structure G x y →
    1-cell-large-globular-structure G y x
  sym-1-cell-is-symmetric-large-globular-structure {x = x} {y} =
    is-symmetric-1-cell-is-symmetric-large-globular-structure r x y

  sym-2-cell-is-symmetric-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f g : 1-cell-large-globular-structure G x y} →
    2-cell-large-globular-structure G f g →
    2-cell-large-globular-structure G g f
  sym-2-cell-is-symmetric-large-globular-structure {x = x} {y} {f} {g} =
    is-symmetric-1-cell-is-symmetric-globular-structure
      ( is-symmetric-globular-structure-1-cell-is-symmetric-large-globular-structure
        ( r)
        ( x)
        ( y))
      ( f)
      ( g)
```
