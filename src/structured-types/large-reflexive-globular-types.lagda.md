# Large reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.universe-levels

open import structured-types.large-globular-types
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A [large globular type](structured-types.large-globular-types.md) is
{{#concept "reflexive" Disambiguation="large globular type" Agda=is-reflexive-large-globular-structure}}
if every $n$-cell `x` comes with a choice of $(n+1)$-cell from `x` to `x`.

## Definition

### Reflexivity structure on a large globular structure

```agda
record
  is-reflexive-large-globular-structure
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A) : UUω
  where

  field
    is-reflexive-1-cell-is-reflexive-large-globular-structure :
      is-reflexive-Large-Relation A (1-cell-large-globular-structure G)

    is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      is-reflexive-globular-structure
        ( globular-structure-1-cell-large-globular-structure G x y)

open is-reflexive-large-globular-structure public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  {G : large-globular-structure β A}
  (r : is-reflexive-large-globular-structure G)
  where

  refl-1-cell-is-reflexive-large-globular-structure :
    {l : Level} {x : A l} → 1-cell-large-globular-structure G x x
  refl-1-cell-is-reflexive-large-globular-structure {x = x} =
    is-reflexive-1-cell-is-reflexive-large-globular-structure r x

  refl-2-cell-is-reflexive-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f : 1-cell-large-globular-structure G x y} →
    2-cell-large-globular-structure G f f
  refl-2-cell-is-reflexive-large-globular-structure {x = x} {y} {f} =
    is-reflexive-1-cell-is-reflexive-globular-structure
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
        ( r)
        ( x)
        ( y))
      ( f)

  refl-3-cell-is-reflexive-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f g : 1-cell-large-globular-structure G x y} →
    {H : 2-cell-large-globular-structure G f g} →
    3-cell-large-globular-structure G H H
  refl-3-cell-is-reflexive-large-globular-structure {x = x} {y} =
    refl-2-cell-is-reflexive-globular-structure
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
        ( r)
        ( x)
        ( y))
```
