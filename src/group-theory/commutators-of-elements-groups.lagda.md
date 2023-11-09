# Commutators of elements in groups

```agda
module group-theory.commutators-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.conjugation
open import group-theory.groups
```

</details>

## Idea

The **commutator** of two elements `x` and `y` of a
[group](group-theory.groups.md) `G` is defined to be the element
`[x,y] = (xy)(yx)⁻¹`. The commutator of two elements `x` and `y` is equal to the
unit if and only if `x` and `y` commute.

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

**Proof:** By transposing identifications along the group operation, we have an
[equivalence](foundation.equivalences.md) `(xy ＝ yx) ≃ ((xy)(yx)⁻¹ ＝ e)`.

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

**Proof:** Since `(uv⁻¹)⁻¹ ＝ vu⁻¹` for any two elements `u,v : G` it follows
that `((xy)(yx)⁻¹)⁻¹ ＝ (yx)(xy)⁻¹`.

```agda
  inv-commutator-Group :
    (x y : type-Group G) →
    inv-Group G (commutator-Group G x y) ＝ commutator-Group G y x
  inv-commutator-Group x y =
    inv-right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

### Conjugation distributes over the commutator

**Proof:** The proof is a simple computation, using the fact that conjugation
distributes over multiplication and preserves inverses:

```text
  u(xy)(yx)⁻¹u⁻¹
  ＝ u(xy)u⁻¹u(yx)⁻¹u⁻¹
  ＝ ((uxu⁻¹)(uyu⁻¹))(u(yx)u⁻¹)⁻¹
  ＝ ((uxu⁻¹)(uyu⁻¹))((uyu⁻¹)(uxu⁻¹))⁻¹.
```

```agda
module _
  {l : Level} (G : Group l)
  where

  distributive-conjugation-commutator-Group :
    (u x y : type-Group G) →
    conjugation-Group G u (commutator-Group G x y) ＝
    commutator-Group G (conjugation-Group G u x) (conjugation-Group G u y)
  distributive-conjugation-commutator-Group u x y =
    ( distributive-conjugation-mul-Group G u _ _) ∙
    ( ap-mul-Group G
      ( distributive-conjugation-mul-Group G u x y)
      ( ( conjugation-inv-Group G u _) ∙
        ( ap (inv-Group G) (distributive-conjugation-mul-Group G u y x))))
```

## External links

- [Commutator](https://www.wikidata.org/wiki/Q2989763) at Wikidata
- [Commutator](https://en.wikipedia.org/wiki/Commutator#Group_theory) at
  Wikipedia
- [Commutator](https://mathworld.wolfram.com/Commutator.html) at Wolfram
  Mathworld
- [Group commutator](https://ncatlab.org/nlab/show/group+commutator) at $n$Lab
