# Multiples of elements in rings

```agda
module ring-theory.multiples-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.multiples-of-elements-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

For any [ring](ring-theory.rings.md) `R` there is a multiplication operation
`ℕ → R → R`, which we write informally as `n x ↦ n · x`. This operation is
defined by [iteratively](foundation.iterating-functions.md) adding `x` with
itself `n` times.

## Definition

### Natural number multiples of ring elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-Ring : ℕ → type-Ring R → type-Ring R
  multiple-Ring = multiple-Ab (ab-Ring R)
```

### The predicate of being a natural multiple of an element in an ring

We say that an element `y` **is a multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`nx ＝ y`.

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-multiple-of-element-prop-Ring :
    (x y : type-Ring R) → Prop l
  is-multiple-of-element-prop-Ring =
    is-multiple-of-element-prop-Ab (ab-Ring R)

  is-multiple-of-element-Ring :
    (x y : type-Ring R) → UU l
  is-multiple-of-element-Ring =
    is-multiple-of-element-Ab (ab-Ring R)

  is-prop-is-multiple-of-element-Ring :
    (x y : type-Ring R) →
    is-prop (is-multiple-of-element-Ring x y)
  is-prop-is-multiple-of-element-Ring =
    is-prop-is-multiple-of-element-Ab (ab-Ring R)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-zero-Ring :
    (n : ℕ) → multiple-Ring R n (zero-Ring R) ＝ zero-Ring R
  multiple-zero-Ring = multiple-zero-Ab (ab-Ring R)
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-succ-Ring :
    (n : ℕ) (x : type-Ring R) →
    multiple-Ring R (succ-ℕ n) x ＝ add-Ring R (multiple-Ring R n x) x
  multiple-succ-Ring = multiple-succ-Ab (ab-Ring R)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-succ-Ring' :
    (n : ℕ) (x : type-Ring R) →
    multiple-Ring R (succ-ℕ n) x ＝ add-Ring R x (multiple-Ring R n x)
  multiple-succ-Ring' = multiple-succ-Ab' (ab-Ring R)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-distributive-multiple-add-Ring :
    (m n : ℕ) {x : type-Ring R} →
    multiple-Ring R (m +ℕ n) x ＝
    add-Ring R (multiple-Ring R m x) (multiple-Ring R n x)
  right-distributive-multiple-add-Ring =
    right-distributive-multiple-add-Ab (ab-Ring R)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-multiple-add-Ring :
    (n : ℕ) {x y : type-Ring R} →
    multiple-Ring R n (add-Ring R x y) ＝
    add-Ring R (multiple-Ring R n x) (multiple-Ring R n y)
  left-distributive-multiple-add-Ring =
    left-distributive-multiple-add-Ab (ab-Ring R)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-mul-Ring :
    (m n : ℕ) {x : type-Ring R} →
    multiple-Ring R (m *ℕ n) x ＝ multiple-Ring R n (multiple-Ring R m x)
  multiple-mul-Ring = multiple-mul-Ab (ab-Ring R)
```
