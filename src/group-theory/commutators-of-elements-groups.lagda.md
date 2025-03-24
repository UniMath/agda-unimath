# Commutators of elements in groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.commutators-of-elements-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.commuting-elements-groups funext univalence truncations
open import group-theory.conjugation funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.homomorphisms-groups funext univalence truncations
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

### Group homomorphisms preserve commutators

**Proof:** Consider a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → H` and two elements `x y : G`. Then we calculate

```text
  f([x,y]) ≐ f((xy)(yx)⁻¹)
           = f(xy)f(yx)⁻¹
           = (f(x)f(y))(f(y)f(x))⁻¹
           ≐ [f(x),f(y)].
```

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-commutator-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (commutator-Group G x y) ＝
    commutator-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-commutator-hom-Group =
    ( preserves-right-div-hom-Group G H f) ∙
    ( ap-right-div-Group H
      ( preserves-mul-hom-Group G H f)
      ( preserves-mul-hom-Group G H f))
```

## External links

- [Commutator](https://www.wikidata.org/wiki/Q2989763) at Wikidata
- [Commutator](https://en.wikipedia.org/wiki/Commutator#Group_theory) at
  Wikipedia
- [Commutator](https://mathworld.wolfram.com/Commutator.html) at Wolfram
  MathWorld
- [Group commutator](https://ncatlab.org/nlab/show/group+commutator) at $n$Lab
