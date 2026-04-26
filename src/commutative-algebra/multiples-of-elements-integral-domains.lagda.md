# Multiples of elements in integral domains

```agda
module commutative-algebra.multiples-of-elements-integral-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.integral-domains
open import commutative-algebra.multiples-of-elements-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

For any [integral domain](commutative-algebra.integral-domains.md) `R` there is
a multiplication operation `ℕ → R → R`, which we write informally as
`n x ↦ n · x`, called taking a
{{#concept "multiple" Disambiguation="of an element of an integral domain, natural number" Agda=multiple-Integral-Domain}}
of `x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  multiple-Integral-Domain :
    ℕ → type-Integral-Domain R → type-Integral-Domain R
  multiple-Integral-Domain =
    multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)

  ap-multiple-Integral-Domain :
    {m n : ℕ} {x y : type-Integral-Domain R} →
    (m ＝ n) → (x ＝ y) →
    multiple-Integral-Domain m x ＝
    multiple-Integral-Domain n y
  ap-multiple-Integral-Domain =
    ap-multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)
```

## Properties

### Zero laws

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  left-zero-law-multiple-Integral-Domain :
    (x : type-Integral-Domain R) →
    multiple-Integral-Domain R 0 x ＝ zero-Integral-Domain R
  left-zero-law-multiple-Integral-Domain =
    left-zero-law-multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)

  right-zero-law-multiple-Integral-Domain :
    (n : ℕ) →
    multiple-Integral-Domain R n (zero-Integral-Domain R) ＝
    zero-Integral-Domain R
  right-zero-law-multiple-Integral-Domain =
    right-zero-law-multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)
```

### `1 · x ＝ x`

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  left-unit-law-multiple-Integral-Domain :
    (x : type-Integral-Domain R) →
    multiple-Integral-Domain R 1 x ＝ x
  left-unit-law-multiple-Integral-Domain x = refl
```

### `(n · x) * y = n · (x * y)`

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  left-mul-multiple-Integral-Domain :
    (n : ℕ) (x y : type-Integral-Domain R) →
    mul-Integral-Domain R (multiple-Integral-Domain R n x) y ＝
    multiple-Integral-Domain R n (mul-Integral-Domain R x y)
  left-mul-multiple-Integral-Domain =
    left-mul-multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)
```

### `x * (n · y) = n · (x * y)`

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  right-mul-multiple-Integral-Domain :
    (n : ℕ) (x y : type-Integral-Domain R) →
    mul-Integral-Domain R x (multiple-Integral-Domain R n y) ＝
    multiple-Integral-Domain R n (mul-Integral-Domain R x y)
  right-mul-multiple-Integral-Domain =
    right-mul-multiple-Commutative-Ring
      ( commutative-ring-Integral-Domain R)
```

### Distributive laws of multiples over addition

```agda
module _
  {l : Level}
  (R : Integral-Domain l)
  where

  left-distributive-multiple-add-Integral-Domain :
    (n : ℕ) {x y : type-Integral-Domain R} →
    multiple-Integral-Domain R n (add-Integral-Domain R x y) ＝
    add-Integral-Domain R
      ( multiple-Integral-Domain R n x)
      ( multiple-Integral-Domain R n y)
  left-distributive-multiple-add-Integral-Domain =
    left-distributive-multiple-add-Commutative-Ring
      ( commutative-ring-Integral-Domain R)

  right-distributive-multiple-add-Integral-Domain :
    (m n : ℕ) {x : type-Integral-Domain R} →
    multiple-Integral-Domain R (m +ℕ n) x ＝
    add-Integral-Domain R
      ( multiple-Integral-Domain R m x)
      ( multiple-Integral-Domain R n x)
  right-distributive-multiple-add-Integral-Domain =
    right-distributive-multiple-add-Commutative-Ring
      ( commutative-ring-Integral-Domain R)
```
