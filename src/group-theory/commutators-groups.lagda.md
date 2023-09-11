# Commutators of elements in groups

```agda
module group-theory.commutators-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
```

</details>

## Idea

A commutator gives an indication of the extent to which a group multiplication
fails to be commutative.

The commutator of two elements, g and h, of a group G, is the element
`[g, h] = (gh)(hg)⁻¹`.

https://en.wikipedia.org/wiki/Commutator#Group_theory

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  commutator-Group : type-Group G → type-Group G → type-Group G
  commutator-Group x y = right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

## Properties

### The commutator of `x` and `y` is unit if and only `x` and `y` commutes

```agda
module _
  {l : Level} (G : Group l)
  where

  is-unit-commutator-commute-Group :
    (x y : type-Group G) →
    commute-Group G x y → is-unit-Group G (commutator-Group G x y)
  is-unit-commutator-commute-Group x y H =
    is-unit-right-div-eq-Group G H

  commute-is-unit-commutator-Group :
    (x y : type-Group G) →
    is-unit-Group G (commutator-Group G x y) → commute-Group G x y
  commute-is-unit-commutator-Group x y H =
    eq-is-unit-right-div-Group G H
```

### The inverse of the commutator `[x,y]` is `[y,x]`

```agda
  inv-commutator-Group :
    (x y : type-Group G) →
    inv-Group G (commutator-Group G x y) ＝ commutator-Group G y x
  inv-commutator-Group x y =
    inv-right-div-Group G (mul-Group G x y) (mul-Group G y x)
```
