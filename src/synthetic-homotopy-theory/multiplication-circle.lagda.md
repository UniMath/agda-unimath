---
title: The multiplication operation on the circle
---

Contributors: Egbert Rijke.

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.multiplication-circle where

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.circle
```

## Idea

Classically, the circle can be viewed as the subset of the complex numbers of absolute value 1. The absolute value of a product of complex numbers is the product of their absolute values. This implies that when we multiply two complex numbers on the unit circle, the result is a complex number on the unit circle. This multiplicative structure carries over to the homotopy type of the circle.

## Definition

### Homotopy `id ~ id` of degree one

```agda
htpy-id-id-ฮ -๐ยน :
  ฮ -๐ยน
    ( eq-value id id)
    ( loop-๐ยน)
    ( tr-eq-value-id-id loop-๐ยน loop-๐ยน loop-๐ยน refl)
htpy-id-id-ฮ -๐ยน =
  apply-dependent-universal-property-๐ยน
    ( eq-value id id)
    ( loop-๐ยน)
    ( tr-eq-value-id-id loop-๐ยน loop-๐ยน loop-๐ยน refl)

htpy-id-id-๐ยน : (x : ๐ยน) โ Id x x
htpy-id-id-๐ยน = pr1 htpy-id-id-ฮ -๐ยน

htpy-id-id-base-๐ยน : Id (htpy-id-id-๐ยน base-๐ยน) loop-๐ยน
htpy-id-id-base-๐ยน = pr1 (pr2 htpy-id-id-ฮ -๐ยน)
```

### Multiplication on the circle

```agda
Mul-ฮ -๐ยน : ๐ยน โ UU lzero
Mul-ฮ -๐ยน x = ๐ยน-Pointed-Type โ* (pair ๐ยน x)

path-over-Mul-ฮ -๐ยน :
  {x : ๐ยน} (p : Id base-๐ยน x) (q : Mul-ฮ -๐ยน base-๐ยน) (r : Mul-ฮ -๐ยน x) โ
  (H : pr1 q ~ pr1 r) โ Id (pr2 q โ p) (H base-๐ยน โ pr2 r) โ
  Id (tr Mul-ฮ -๐ยน p q) r
path-over-Mul-ฮ -๐ยน {x} refl q r H u =
  eq-htpy-pointed-map
    ( ๐ยน-Pointed-Type)
    ( ๐ยน-Pointed-Type)
    ( q)
    ( r)
    ( pair H (con-inv (H base-๐ยน) (pr2 r) (pr2 q) (inv (inv right-unit โ u))))

eq-id-id-๐ยน-Pointed-Type :
  Id (tr Mul-ฮ -๐ยน loop-๐ยน id-pointed-map) id-pointed-map
eq-id-id-๐ยน-Pointed-Type =
  path-over-Mul-ฮ -๐ยน loop-๐ยน
    ( id-pointed-map)
    ( id-pointed-map)
    ( htpy-id-id-๐ยน)
    ( inv htpy-id-id-base-๐ยน โ inv right-unit)

mul-ฮ -๐ยน :
  ฮ -๐ยน ( Mul-ฮ -๐ยน)
       ( id-pointed-map)
       ( eq-id-id-๐ยน-Pointed-Type)
mul-ฮ -๐ยน =
  apply-dependent-universal-property-๐ยน
    ( Mul-ฮ -๐ยน)
    ( id-pointed-map)
    ( eq-id-id-๐ยน-Pointed-Type)

mul-๐ยน : ๐ยน โ ๐ยน โ ๐ยน
mul-๐ยน x = pr1 (pr1 mul-ฮ -๐ยน x)

left-unit-law-mul-๐ยน : (x : ๐ยน) โ Id (mul-๐ยน base-๐ยน x) x
left-unit-law-mul-๐ยน = htpy-eq (ap pr1 (pr1 (pr2 mul-ฮ -๐ยน)))

right-unit-law-mul-๐ยน : (x : ๐ยน) โ Id (mul-๐ยน x base-๐ยน) x
right-unit-law-mul-๐ยน x = pr2 (pr1 mul-ฮ -๐ยน x)
```
