# The ring of complex numbers

```agda
module complex-numbers.ring-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import complex-numbers.additive-group-of-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

The type of [complex numbers](complex-numbers.complex-numbers.md) equipped with
[multiplication](complex-numbers.multiplication-complex-numbers.md) and
[addition](complex-numbers.addition-complex-numbers.md) is a
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
ring-ℂ-lzero : Ring (lsuc lzero)
ring-ℂ-lzero =
  ( ab-add-ℂ-lzero ,
    ( mul-ℂ , associative-mul-ℂ) ,
    ( one-ℂ , left-unit-law-mul-ℂ , right-unit-law-mul-ℂ) ,
    left-distributive-mul-add-ℂ ,
    right-distributive-mul-add-ℂ)

commutative-ring-ℂ-lzero : Commutative-Ring (lsuc lzero)
commutative-ring-ℂ-lzero =
  ( ring-ℂ-lzero ,
    commutative-mul-ℂ)
```
