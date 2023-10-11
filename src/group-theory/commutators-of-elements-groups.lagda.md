# Commutators of elements in groups

```agda
module group-theory.commutators-of-elements-groups where
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

The **commutator** of two elements `g` and `h` of a
[group](group-theory.groups.md) `G` is defined to be the element
`[g, h] = (gh)(hg)⁻¹`. The commutator of two elements `g` and `h` is equal to
the unit if and only if `g` and `h` commute.

## Definition

### The commutator operation

```agda
module _
  {l : Level} (G : Group l)
  where

  commutator-Group : type-Group G → type-Group G → type-Group G
  commutator-Group x y = right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

## Properties

### The commutator of `x` and `y` is the unit element if and only `x` and `y` commute

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

## External links

- [Commutator](https://en.wikipedia.org/wiki/Commutator#Group_theory) at
  Wikipedia
- [Group commutator](https://ncatlab.org/nlab/show/group+commutator) at nlab
