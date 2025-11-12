# Multiples of elements in commutative semirings

```agda
module commutative-algebra.multiples-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.multiples-of-elements-semirings
```

</details>

## Idea

For any [commutative semiring](commutative-algebra.commutative-semirings.md) `R`
there is a multiplication operation `ℕ → R → R`, which we write informally as
`n x ↦ n · x`, called taking a
{{#concept "multiple" Disambiguation="of an element of a commutative semiring, natural number" Agda=multiple-Commutative-Semiring}}
of `x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  multiple-Commutative-Semiring :
    ℕ → type-Commutative-Semiring R → type-Commutative-Semiring R
  multiple-Commutative-Semiring =
    multiple-Semiring (semiring-Commutative-Semiring R)

  ap-multiple-Commutative-Semiring :
    {m n : ℕ} {x y : type-Commutative-Semiring R} →
    (m ＝ n) → (x ＝ y) →
    multiple-Commutative-Semiring m x ＝
    multiple-Commutative-Semiring n y
  ap-multiple-Commutative-Semiring =
    ap-multiple-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### Zero laws

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  left-zero-law-multiple-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    multiple-Commutative-Semiring R 0 x ＝ zero-Commutative-Semiring R
  left-zero-law-multiple-Commutative-Semiring =
    left-zero-law-multiple-Semiring (semiring-Commutative-Semiring R)

  right-zero-law-multiple-Commutative-Semiring :
    (n : ℕ) →
    multiple-Commutative-Semiring R n (zero-Commutative-Semiring R) ＝
    zero-Commutative-Semiring R
  right-zero-law-multiple-Commutative-Semiring =
    right-zero-law-multiple-Semiring (semiring-Commutative-Semiring R)
```

### Unit laws

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  left-unit-law-multiple-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    multiple-Commutative-Semiring R 1 x ＝ x
  left-unit-law-multiple-Commutative-Semiring =
    left-unit-law-multiple-Semiring (semiring-Commutative-Semiring R)
```

### `(n ∙ x) * y ＝ n ∙ (x * y)`

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  left-mul-multiple-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (multiple-Commutative-Semiring R n x) y ＝
    multiple-Commutative-Semiring R n (mul-Commutative-Semiring R x y)
  left-mul-multiple-Commutative-Semiring =
    left-mul-multiple-Semiring (semiring-Commutative-Semiring R)
```

### `x * (n ∙ y) * y ＝ n ∙ (x * y)`

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  right-mul-multiple-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R x (multiple-Commutative-Semiring R n y) ＝
    multiple-Commutative-Semiring R n (mul-Commutative-Semiring R x y)
  right-mul-multiple-Commutative-Semiring =
    right-mul-multiple-Semiring (semiring-Commutative-Semiring R)
```

### Distributive laws of multiplication over addition

```agda
module _
  {l : Level}
  (R : Commutative-Semiring l)
  where

  left-distributive-multiple-add-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring R) →
    multiple-Commutative-Semiring R n (add-Commutative-Semiring R x y) ＝
    add-Commutative-Semiring R
      ( multiple-Commutative-Semiring R n x)
      ( multiple-Commutative-Semiring R n y)
  left-distributive-multiple-add-Commutative-Semiring =
    left-distributive-multiple-add-Semiring
      ( semiring-Commutative-Semiring R)

  right-distributive-multiple-add-Commutative-Semiring :
    (m n : ℕ) (x : type-Commutative-Semiring R) →
    multiple-Commutative-Semiring R (m +ℕ n) x ＝
    add-Commutative-Semiring R
      ( multiple-Commutative-Semiring R m x)
      ( multiple-Commutative-Semiring R n x)
  right-distributive-multiple-add-Commutative-Semiring =
    right-distributive-multiple-add-Semiring
      ( semiring-Commutative-Semiring R)
```
