# Multiples of elements in rings

```agda
module ring-theory.multiples-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.multiples-of-elements-abelian-groups

open import ring-theory.multiples-of-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

For any [ring](ring-theory.rings.md) `R` there is a multiplication operation
`ℕ → R → R`, which we write informally as `n x ↦ n · x`, called taking a
{{#concept "multiple" Disambiguation="of an element of a ring, natural number" Agda=multiple-Ring}}
of `x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

### Natural number multiples of ring elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  multiple-Ring : ℕ → type-Ring R → type-Ring R
  multiple-Ring = multiple-Ab (ab-Ring R)

  ap-multiple-Ring :
    {m n : ℕ} {x y : type-Ring R} →
    (m ＝ n) → (x ＝ y) → multiple-Ring m x ＝ multiple-Ring n y
  ap-multiple-Ring m=n = ap-binary multiple-Ring m=n
```

### The predicate of being a natural multiple of an element in an ring

We say that an element `y` **is a multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) a natural number `n` such
that `nx ＝ y`.

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

  right-zero-law-multiple-Ring :
    (n : ℕ) → multiple-Ring R n (zero-Ring R) ＝ zero-Ring R
  right-zero-law-multiple-Ring = multiple-zero-Ab (ab-Ring R)
```

### `0 · r ＝ r`

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-zero-law-multiple-Ring :
    (r : type-Ring R) → multiple-Ring R 0 r ＝ zero-Ring R
  left-zero-law-multiple-Ring _ = refl
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

### `(n · x) * y ＝ n · (x * y)`

```agda
module _
  {l : Level}
  (R : Ring l)
  where

  left-mul-multiple-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R (multiple-Ring R n x) y ＝ multiple-Ring R n (mul-Ring R x y)
  left-mul-multiple-Ring = left-mul-multiple-Semiring (semiring-Ring R)
```

### `x * (n · y) ＝ n · (x * y)`

```agda
module _
  {l : Level}
  (R : Ring l)
  where

  right-mul-multiple-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R x (multiple-Ring R n y) ＝ multiple-Ring R n (mul-Ring R x y)
  right-mul-multiple-Ring = right-mul-multiple-Semiring (semiring-Ring R)
```
