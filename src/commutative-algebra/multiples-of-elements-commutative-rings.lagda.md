# Multiples of elements in commutative rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.multiples-of-elements-commutative-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types funext
open import foundation.universe-levels

open import ring-theory.multiples-of-elements-rings funext univalence truncations
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
  multiple-Commutative-Ring =
    multiple-Ring (ring-Commutative-Ring A)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  multiple-zero-Commutative-Ring :
    (n : ℕ) →
    multiple-Commutative-Ring A n (zero-Commutative-Ring A) ＝
    zero-Commutative-Ring A
  multiple-zero-Commutative-Ring =
    multiple-zero-Ring (ring-Commutative-Ring A)
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
