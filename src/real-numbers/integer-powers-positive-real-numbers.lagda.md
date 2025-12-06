# Integer powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.integer-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.integer-multiples-of-elements-large-abelian-groups
open import group-theory.integer-powers-of-elements-large-groups

open import real-numbers.large-multiplicative-group-of-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of ℝ⁺ to an integer power" Agda=int-power-ℝ⁺}}
on the [positive real numbers](real-numbers.positive-real-numbers.md) `x ↦ xᵏ`
is defined by [iteratively](foundation.iterating-functions.md)
[multiplying](real-numbers.multiplication-positive-real-numbers.md) `x` with
itself `k` times. On this page we consider the case where `k` is an
[integer](elementary-number-theory.integers.md).

## Definition

```agda
int-power-ℝ⁺ : {l : Level} → ℤ → ℝ⁺ l → ℝ⁺ l
int-power-ℝ⁺ = int-multiple-Large-Ab large-ab-mul-ℝ⁺
```

## Properties

### `x¹ = x`

```agda
abstract
  int-one-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → int-power-ℝ⁺ one-ℤ x ＝ x
  int-one-power-ℝ⁺ = int-multiple-one-Large-Ab large-ab-mul-ℝ⁺
```

### `x⁻¹` is the multiplicative inverse of `x`

```agda
abstract
  int-neg-one-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → int-power-ℝ⁺ neg-one-ℤ x ＝ inv-ℝ⁺ x
  int-neg-one-power-ℝ⁺ = int-multiple-neg-one-Large-Ab large-ab-mul-ℝ⁺
```

### `x⁻ᵏ` is the multiplicative inverse of `xᵏ`

```agda
abstract
  int-neg-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    int-power-ℝ⁺ (neg-ℤ k) x ＝ inv-ℝ⁺ (int-power-ℝ⁺ k x)
  int-neg-power-ℝ⁺ = int-multiple-neg-Large-Ab large-ab-mul-ℝ⁺
```

### Integer powers agree with natural powers

```agda
abstract
  int-power-int-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) → int-power-ℝ⁺ (int-ℕ n) x ＝ power-ℝ⁺ n x
  int-power-int-ℝ⁺ {l} 0 (x , _) = eq-ℝ⁺ _ _ (ap (raise-ℝ l) refl)
  int-power-int-ℝ⁺ 1 x = eq-ℝ⁺ _ _ (ap real-ℝ⁺ (int-one-power-ℝ⁺ x))
  int-power-int-ℝ⁺ (succ-ℕ n@(succ-ℕ _)) x⁺@(x , _) =
    equational-reasoning
      int-power-ℝ⁺ (int-ℕ (succ-ℕ n)) x⁺
      ＝ int-power-ℝ⁺ (succ-ℤ (int-ℕ n)) x⁺
        by ap-binary int-power-ℝ⁺ (inv (succ-int-ℕ n)) refl
      ＝ int-power-ℝ⁺ (int-ℕ n) x⁺ *ℝ⁺ x⁺
        by int-multiple-succ-Large-Ab large-ab-mul-ℝ⁺ (int-ℕ n) x⁺
      ＝ power-ℝ⁺ n x⁺ *ℝ⁺ x⁺
        by ap-mul-ℝ⁺ (int-power-int-ℝ⁺ n x⁺) (eq-ℝ⁺ _ _ refl)
      ＝ power-ℝ⁺ (succ-ℕ n) x⁺
        by eq-ℝ⁺ _ _ (refl {x = power-ℝ (succ-ℕ n) x})
```

### `1ⁿ = 1`

```agda
abstract
  int-power-raise-one-ℝ⁺ :
    (l : Level) (k : ℤ) →
    int-power-ℝ⁺ k (raise-ℝ⁺ l one-ℝ⁺) ＝ raise-ℝ⁺ l one-ℝ⁺
  int-power-raise-one-ℝ⁺ =
    right-zero-law-int-multiple-Large-Ab large-ab-mul-ℝ⁺

  int-power-one-ℝ⁺ :
    (k : ℤ) → int-power-ℝ⁺ k one-ℝ⁺ ＝ one-ℝ⁺
  int-power-one-ℝ⁺ k =
    ( ap (int-power-ℝ⁺ k) (eq-raise-ℝ⁺ one-ℝ⁺)) ∙
    ( int-power-raise-one-ℝ⁺ lzero k) ∙
    ( inv (eq-raise-ℝ⁺ one-ℝ⁺))
```

### `xⁿ⁺¹ = xⁿx = xxⁿ`

```agda
module _
  {l : Level} (k : ℤ) (x : ℝ⁺ l)
  where

  abstract
    int-power-succ-ℝ⁺ :
      int-power-ℝ⁺ (succ-ℤ k) x ＝ int-power-ℝ⁺ k x *ℝ⁺ x
    int-power-succ-ℝ⁺ =
      int-multiple-succ-Large-Ab large-ab-mul-ℝ⁺ k x

    int-power-succ-ℝ⁺' :
      int-power-ℝ⁺ (succ-ℤ k) x ＝ x *ℝ⁺ int-power-ℝ⁺ k x
    int-power-succ-ℝ⁺' =
      int-multiple-succ-Large-Ab' large-ab-mul-ℝ⁺ k x
```

### `xⁿ⁻¹ = xⁿx⁻¹ = x⁻¹x`

```agda
module _
  {l : Level} (k : ℤ) (x : ℝ⁺ l)
  where

  abstract
    int-power-pred-ℝ⁺ :
      int-power-ℝ⁺ (pred-ℤ k) x ＝ int-power-ℝ⁺ k x *ℝ⁺ inv-ℝ⁺ x
    int-power-pred-ℝ⁺ =
      int-multiple-pred-Large-Ab large-ab-mul-ℝ⁺ k x

    int-power-pred-ℝ⁺' :
      int-power-ℝ⁺ (pred-ℤ k) x ＝ inv-ℝ⁺ x *ℝ⁺ int-power-ℝ⁺ k x
    int-power-pred-ℝ⁺' =
      int-multiple-pred-Large-Ab' large-ab-mul-ℝ⁺ k x
```

### `xᵐ⁺ⁿ = xᵐxⁿ`

```agda
abstract
  distributive-int-power-add-ℝ⁺ :
    {l : Level} (m n : ℤ) (x : ℝ⁺ l) →
    int-power-ℝ⁺ (m +ℤ n) x ＝ int-power-ℝ⁺ m x *ℝ⁺ int-power-ℝ⁺ n x
  distributive-int-power-add-ℝ⁺ m n x =
    right-distributive-int-multiple-add-Large-Ab large-ab-mul-ℝ⁺ x m n
```

### `xᵐⁿ = (xᵐ)ⁿ`

```agda
abstract
  int-power-mul-ℝ⁺ :
    {l : Level} (m n : ℤ) (x : ℝ⁺ l) →
    int-power-ℝ⁺ (m *ℤ n) x ＝ int-power-ℝ⁺ n (int-power-ℝ⁺ m x)
  int-power-mul-ℝ⁺ = int-multiple-mul-Large-Ab large-ab-mul-ℝ⁺
```

### `(xy)ᵏ = xᵏyᵏ`

```agda
abstract
  distributive-int-power-mul-ℝ⁺ :
    {l1 l2 : Level} (k : ℤ) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    int-power-ℝ⁺ k (x *ℝ⁺ y) ＝ int-power-ℝ⁺ k x *ℝ⁺ int-power-ℝ⁺ k y
  distributive-int-power-mul-ℝ⁺ =
    left-distributive-int-multiple-add-Large-Ab large-ab-mul-ℝ⁺
```

### `(xⁿ)ᵐ = (xᵐ)ⁿ`

```agda
abstract
  commute-int-power-ℝ⁺ :
    {l : Level} (m n : ℤ) (x : ℝ⁺ l) →
    int-power-ℝ⁺ m (int-power-ℝ⁺ n x) ＝ int-power-ℝ⁺ n (int-power-ℝ⁺ m x)
  commute-int-power-ℝ⁺ =
    commute-int-power-Large-Group large-group-mul-ℝ⁺
```

## See also

- [Natural powers of real numbers](real-numbers.powers-real-numbers.md)
