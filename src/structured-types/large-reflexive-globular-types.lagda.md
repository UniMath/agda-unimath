# Large reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
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

### Reflexivity structure on large globular types

```agda
record
  is-reflexive-Large-Globular-Type
    {α : Level → Level} {β : Level → Level → Level}
    (A : Large-Globular-Type α β) :
    UUω
  where
  field
    refl-0-cell-is-reflexive-Large-Globular-Type :
      is-reflexive-Large-Relation
        ( 0-cell-Large-Globular-Type A)
        ( 1-cell-Large-Globular-Type A)
    is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Globular-Type A l1}
      {y : 0-cell-Large-Globular-Type A l2} →
      is-reflexive-Globular-Type
        ( 1-cell-globular-type-Large-Globular-Type A x y)

  refl-1-cell-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    is-reflexive (2-cell-Large-Globular-Type A {x = x} {y = y})
  refl-1-cell-is-reflexive-Large-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type
      ( 1-cell-globular-type-Large-Globular-Type A _ _)
      ( is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type)

  refl-2-cell-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {f g : 1-cell-Large-Globular-Type A x y} →
    is-reflexive (3-cell-Large-Globular-Type A {f = f} {g = g})
  refl-2-cell-is-reflexive-Large-Globular-Type =
    is-reflexive-2-cell-is-reflexive-Globular-Type
      ( 1-cell-globular-type-Large-Globular-Type A _ _)
      ( is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type)

open is-reflexive-Large-Globular-Type public
```

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
