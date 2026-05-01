# Multiples of elements in commutative rings

```agda
module commutative-algebra.multiples-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.multiples-of-elements-rings
```

</details>

## Idea

For any [commutative ring](commutative-algebra.commutative-rings.md) `A` there
is a multiplication operation `ℕ → A → A`, which we write informally as
`n x ↦ n · x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

### Natural number multiples of elements of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  multiple-Commutative-Ring :
    ℕ → type-Commutative-Ring A → type-Commutative-Ring A
  multiple-Commutative-Ring = multiple-Ring (ring-Commutative-Ring A)

  ap-multiple-Commutative-Ring :
    {m n : ℕ} {x y : type-Commutative-Ring A} →
    (m ＝ n) → (x ＝ y) →
    multiple-Commutative-Ring m x ＝
    multiple-Commutative-Ring n y
  ap-multiple-Commutative-Ring = ap-multiple-Ring (ring-Commutative-Ring A)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  right-zero-law-multiple-Commutative-Ring :
    (n : ℕ) →
    multiple-Commutative-Ring A n (zero-Commutative-Ring A) ＝
    zero-Commutative-Ring A
  right-zero-law-multiple-Commutative-Ring =
    right-zero-law-multiple-Ring (ring-Commutative-Ring A)
```

### `0 · n ＝ 0`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-zero-law-multiple-Commutative-Ring :
    (r : type-Commutative-Ring A) →
    multiple-Commutative-Ring A 0 r ＝ zero-Commutative-Ring A
  left-zero-law-multiple-Commutative-Ring _ = refl
```

### Left unit law

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  left-unit-law-multiple-Commutative-Ring :
    (x : type-Commutative-Ring R) →
    multiple-Commutative-Ring R 1 x ＝ x
  left-unit-law-multiple-Commutative-Ring x = refl
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  multiple-succ-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    multiple-Commutative-Ring A (succ-ℕ n) x ＝
    add-Commutative-Ring A (multiple-Commutative-Ring A n x) x
  multiple-succ-Commutative-Ring =
    multiple-succ-Ring (ring-Commutative-Ring A)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  multiple-succ-Commutative-Ring' :
    (n : ℕ) (x : type-Commutative-Ring A) →
    multiple-Commutative-Ring A (succ-ℕ n) x ＝
    add-Commutative-Ring A x (multiple-Commutative-Ring A n x)
  multiple-succ-Commutative-Ring' =
    multiple-succ-Ring' (ring-Commutative-Ring A)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  right-distributive-multiple-add-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    multiple-Commutative-Ring A (m +ℕ n) x ＝
    add-Commutative-Ring A
      ( multiple-Commutative-Ring A m x)
      ( multiple-Commutative-Ring A n x)
  right-distributive-multiple-add-Commutative-Ring =
    right-distributive-multiple-add-Ring (ring-Commutative-Ring A)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-distributive-multiple-add-Commutative-Ring :
    (n : ℕ) {x y : type-Commutative-Ring A} →
    multiple-Commutative-Ring A n (add-Commutative-Ring A x y) ＝
    add-Commutative-Ring A
      ( multiple-Commutative-Ring A n x)
      ( multiple-Commutative-Ring A n y)
  left-distributive-multiple-add-Commutative-Ring =
    left-distributive-multiple-add-Ring (ring-Commutative-Ring A)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  multiple-mul-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    multiple-Commutative-Ring A (m *ℕ n) x ＝
    multiple-Commutative-Ring A n (multiple-Commutative-Ring A m x)
  multiple-mul-Commutative-Ring =
    multiple-mul-Ring (ring-Commutative-Ring A)
```

### `(n · x) * y ＝ n · (x * y)`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  left-mul-multiple-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring R) →
    mul-Commutative-Ring R (multiple-Commutative-Ring R n x) y ＝
    multiple-Commutative-Ring R n (mul-Commutative-Ring R x y)
  left-mul-multiple-Commutative-Ring =
    left-mul-multiple-Ring (ring-Commutative-Ring R)
```

### `x * (n · y) * y ＝ n · (x * y)`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  right-mul-multiple-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring R) →
    mul-Commutative-Ring R x (multiple-Commutative-Ring R n y) ＝
    multiple-Commutative-Ring R n (mul-Commutative-Ring R x y)
  right-mul-multiple-Commutative-Ring =
    right-mul-multiple-Ring (ring-Commutative-Ring R)
```
