# The ring of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.ring-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.additive-group-of-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers

open import ring-theory.rings
```

</details>

## Idea

The [real numbers](real-numbers.dedekind-real-numbers.md) form a
[commutative ring](commutative-algebra.commutative-rings.md) under
[multiplication](real-numbers.multiplication-real-numbers.md) and
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
ring-ℝ-lzero : Ring (lsuc lzero)
ring-ℝ-lzero =
  ( ab-add-ℝ-lzero ,
    ( mul-ℝ , associative-mul-ℝ) ,
    ( one-ℝ , left-unit-law-mul-ℝ , right-unit-law-mul-ℝ) ,
    left-distributive-mul-add-ℝ ,
    right-distributive-mul-add-ℝ)

commutative-ring-ℝ-lzero : Commutative-Ring (lsuc lzero)
commutative-ring-ℝ-lzero =
  ( ring-ℝ-lzero ,
    commutative-mul-ℝ)
```
