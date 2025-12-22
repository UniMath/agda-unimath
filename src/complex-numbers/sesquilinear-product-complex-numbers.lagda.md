# Sesquilinear products of complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.sesquilinear-product-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.zero-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.complex-vector-spaces
open import linear-algebra.sesquilinear-forms-complex-vector-spaces

open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "sesquilinear product" Disambiguation="of complex numbers" Agda=sesquilinear-mul-ℂ}}
of two complex numbers `z` and `w` is the
[product](complex-numbers.multiplication-complex-numbers.md) of `z` and the
[conjugate](complex-numbers.conjugation-complex-numbers.md) of `w`.

## Definition

```agda
sesquilinear-mul-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
sesquilinear-mul-ℂ z w = z *ℂ conjugate-ℂ w
```

## Properties

### The sesquilinear product is conjugate symmetric

```agda
abstract
  is-conjugate-symmetric-sesquilinear-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    sesquilinear-mul-ℂ z w ＝ conjugate-ℂ (sesquilinear-mul-ℂ w z)
  is-conjugate-symmetric-sesquilinear-mul-ℂ z w =
    equational-reasoning
      z *ℂ conjugate-ℂ w
      ＝ conjugate-ℂ (conjugate-ℂ z) *ℂ conjugate-ℂ w
        by ap-mul-ℂ (inv (is-involution-conjugate-ℂ z)) refl
      ＝ conjugate-ℂ (conjugate-ℂ z *ℂ w)
        by inv (conjugate-mul-ℂ (conjugate-ℂ z) w)
      ＝ conjugate-ℂ (w *ℂ conjugate-ℂ z)
        by ap conjugate-ℂ (commutative-mul-ℂ (conjugate-ℂ z) w)
```

### The sesquilinear product is semidefinite

```agda
abstract
  is-semidefinite-sesquilinear-mul-ℂ :
    {l : Level} (z : ℂ l) → is-nonnegative-ℝ (re-ℂ (sesquilinear-mul-ℂ z z))
  is-semidefinite-sesquilinear-mul-ℂ z =
    inv-tr
      ( is-nonnegative-ℝ ∘ re-ℂ)
      ( eq-squared-magnitude-mul-conjugate-ℂ z)
      ( is-nonnegative-squared-magnitude-ℂ z)
```

### The sesquilinear product is extensional

```agda
abstract
  is-extensional-sesquilinear-mul-ℂ :
    {l : Level} (z : ℂ l) → is-zero-ℂ (sesquilinear-mul-ℂ z z) → is-zero-ℂ z
  is-extensional-sesquilinear-mul-ℂ z zz*=0 =
    is-extensional-squared-magnitude-ℂ
      ( z)
      ( pr1 (tr is-zero-ℂ (eq-squared-magnitude-mul-conjugate-ℂ z) zz*=0))
```

### The sesquilinear product is additive on each side

```agda
abstract
  is-left-additive-sesquilinear-mul-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sesquilinear-mul-ℂ (x +ℂ y) z ＝
    sesquilinear-mul-ℂ x z +ℂ sesquilinear-mul-ℂ y z
  is-left-additive-sesquilinear-mul-ℂ x y z =
    right-distributive-mul-add-ℂ x y (conjugate-ℂ z)

  is-right-additive-sesquilinear-mul-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sesquilinear-mul-ℂ x (y +ℂ z) ＝
    sesquilinear-mul-ℂ x y +ℂ sesquilinear-mul-ℂ x z
  is-right-additive-sesquilinear-mul-ℂ x y z =
    ( ap-mul-ℂ refl (conjugate-add-ℂ y z)) ∙
    ( left-distributive-mul-add-ℂ x (conjugate-ℂ y) (conjugate-ℂ z))
```

### The sesquilinear product preserves scalar multiplication on the left

```agda
abstract
  preserves-scalar-mul-left-sesquilinear-mul-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sesquilinear-mul-ℂ (x *ℂ y) z ＝ x *ℂ sesquilinear-mul-ℂ y z
  preserves-scalar-mul-left-sesquilinear-mul-ℂ x y z =
    associative-mul-ℂ x y (conjugate-ℂ z)
```

### The sesquilinear product conjugates scalar multiplication on the right

```agda
abstract
  conjugates-scalar-mul-right-sesquilinear-mul-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sesquilinear-mul-ℂ y (x *ℂ z) ＝ conjugate-ℂ x *ℂ sesquilinear-mul-ℂ y z
  conjugates-scalar-mul-right-sesquilinear-mul-ℂ x y z =
    ( ap-mul-ℂ refl (conjugate-mul-ℂ x z)) ∙
    ( left-swap-mul-ℂ y (conjugate-ℂ x) (conjugate-ℂ z))
```

### The sesquilinear product is a sesquilinear form on the vector space of complex numbers over themselves

```agda
is-sesquilinear-form-sesquilinear-mul-ℂ :
  (l : Level) →
  is-sesquilinear-form-ℂ-Vector-Space
    ( complex-vector-space-ℂ l)
    ( sesquilinear-mul-ℂ)
is-sesquilinear-form-sesquilinear-mul-ℂ l =
  ( is-left-additive-sesquilinear-mul-ℂ ,
    preserves-scalar-mul-left-sesquilinear-mul-ℂ ,
    is-right-additive-sesquilinear-mul-ℂ ,
    conjugates-scalar-mul-right-sesquilinear-mul-ℂ)

sesquilinear-form-sesquilinear-mul-ℂ :
  (l : Level) → sesquilinear-form-ℂ-Vector-Space (complex-vector-space-ℂ l)
sesquilinear-form-sesquilinear-mul-ℂ l =
  ( sesquilinear-mul-ℂ , is-sesquilinear-form-sesquilinear-mul-ℂ l)
```
