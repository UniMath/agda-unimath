# Reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.reflexive-globular-types where
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

A [globular type](structured-types.globular-types.md) is
{{#concept "reflexive" Disambiguation="globular type" Agda=is-reflexive-globular-structure}}
if every $n$-cell `x` comes with a choice of $(n+1)$-cell from `x` to `x`.

## Definition

### Reflexivity structure on a globular structure

```agda
record
  is-reflexive-globular-structure
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    is-reflexive-1-cell-is-reflexive-globular-structure :
      is-reflexive (1-cell-globular-structure G)
    is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure :
      (x y : A) →
      is-reflexive-globular-structure
        ( globular-structure-1-cell-globular-structure G x y)

open is-reflexive-globular-structure public

module _
  {l1 l2 : Level} {A : UU l1} {G : globular-structure l2 A}
  (r : is-reflexive-globular-structure G)
  where

  refl-1-cell-is-reflexive-globular-structure :
    {x : A} → 1-cell-globular-structure G x x
  refl-1-cell-is-reflexive-globular-structure {x} =
    is-reflexive-1-cell-is-reflexive-globular-structure r x

  refl-2-cell-is-reflexive-globular-structure :
    {x y : A} {f : 1-cell-globular-structure G x y} →
    2-cell-globular-structure G f f
  refl-2-cell-is-reflexive-globular-structure {x} {y} {f} =
    is-reflexive-1-cell-is-reflexive-globular-structure
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
        ( r)
        ( x)
        ( y))
      ( f)

  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structure :
    {x y : A}
    (f g : 1-cell-globular-structure G x y) →
    is-reflexive-globular-structure
      ( globular-structure-2-cell-globular-structure G f g)
  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structure
    { x} {y} =
    is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
      ( is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
        ( r)
        ( x)
        ( y))

  refl-3-cell-is-reflexive-globular-structure :
    {x y : A}
    {f g : 1-cell-globular-structure G x y}
    {H : 2-cell-globular-structure G f g} →
    3-cell-globular-structure G H H
  refl-3-cell-is-reflexive-globular-structure {x} {y} {f} {g} {H} =
    is-reflexive-1-cell-is-reflexive-globular-structure
      ( is-reflexive-globular-structure-2-cell-is-reflexive-globular-structure
        ( f)
        ( g))
      ( H)
```

### The type of reflexive globular structures

```agda
reflexive-globular-structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
reflexive-globular-structure l2 A =
  Σ (globular-structure l2 A) (is-reflexive-globular-structure)
```

## Examples

### The reflexive globular structure on a type given by its identity types

```agda
is-reflexive-globular-structure-Id :
  {l : Level} (A : UU l) →
  is-reflexive-globular-structure (globular-structure-Id A)
is-reflexive-globular-structure-Id A =
  λ where
  .is-reflexive-1-cell-is-reflexive-globular-structure x →
    refl
  .is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure x y →
    is-reflexive-globular-structure-Id (x ＝ y)
```
