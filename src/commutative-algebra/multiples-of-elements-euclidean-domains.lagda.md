# Multiples of elements in Euclidean domains

```agda
module commutative-algebra.multiples-of-elements-euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domains
open import commutative-algebra.multiples-of-elements-integral-domains

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

For any [Euclidean domain](commutative-algebra.euclidean-domains.md) `R` there
is a multiplication operation `ℕ → R → R`, which we write informally as
`n x ↦ n · x`, called taking a
{{#concept "multiple" Disambiguation="of an element of a Euclidean domain, natural number" Agda=multiple-Euclidean-Domain}}
of `x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  multiple-Euclidean-Domain :
    ℕ → type-Euclidean-Domain R → type-Euclidean-Domain R
  multiple-Euclidean-Domain =
    multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)

  ap-multiple-Euclidean-Domain :
    {m n : ℕ} {x y : type-Euclidean-Domain R} →
    (m ＝ n) → (x ＝ y) →
    multiple-Euclidean-Domain m x ＝ multiple-Euclidean-Domain n y
  ap-multiple-Euclidean-Domain =
    ap-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```

## Properties

### Zero laws

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  left-zero-law-multiple-Euclidean-Domain :
    (x : type-Euclidean-Domain R) →
    multiple-Euclidean-Domain R 0 x ＝ zero-Euclidean-Domain R
  left-zero-law-multiple-Euclidean-Domain =
    left-zero-law-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)

  right-zero-law-multiple-Euclidean-Domain :
    (n : ℕ) →
    multiple-Euclidean-Domain R n (zero-Euclidean-Domain R) ＝
    zero-Euclidean-Domain R
  right-zero-law-multiple-Euclidean-Domain =
    right-zero-law-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```

### `1 ∙ x = x`

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  left-unit-law-multiple-Euclidean-Domain :
    (x : type-Euclidean-Domain R) →
    multiple-Euclidean-Domain R 1 x ＝ x
  left-unit-law-multiple-Euclidean-Domain =
    left-unit-law-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```

### `(n ∙ x) * y = n ∙ (x * y)`

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  left-mul-multiple-Euclidean-Domain :
    (n : ℕ) (x y : type-Euclidean-Domain R) →
    mul-Euclidean-Domain R (multiple-Euclidean-Domain R n x) y ＝
    multiple-Euclidean-Domain R n (mul-Euclidean-Domain R x y)
  left-mul-multiple-Euclidean-Domain =
    left-mul-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```

### `x * (n ∙ y) = n ∙ (x * y)`

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  right-mul-multiple-Euclidean-Domain :
    (n : ℕ) (x y : type-Euclidean-Domain R) →
    mul-Euclidean-Domain R x (multiple-Euclidean-Domain R n y) ＝
    multiple-Euclidean-Domain R n (mul-Euclidean-Domain R x y)
  right-mul-multiple-Euclidean-Domain =
    right-mul-multiple-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```

### Distributive laws of multiples over addition

```agda
module _
  {l : Level}
  (R : Euclidean-Domain l)
  where

  left-distributive-multiple-add-Euclidean-Domain :
    (n : ℕ) {x y : type-Euclidean-Domain R} →
    multiple-Euclidean-Domain R n (add-Euclidean-Domain R x y) ＝
    add-Euclidean-Domain R
      ( multiple-Euclidean-Domain R n x)
      ( multiple-Euclidean-Domain R n y)
  left-distributive-multiple-add-Euclidean-Domain =
    left-distributive-multiple-add-Integral-Domain
      ( integral-domain-Euclidean-Domain R)

  right-distributive-multiple-add-Euclidean-Domain :
    (m n : ℕ) {x : type-Euclidean-Domain R} →
    multiple-Euclidean-Domain R (m +ℕ n) x ＝
    add-Euclidean-Domain R
      ( multiple-Euclidean-Domain R m x)
      ( multiple-Euclidean-Domain R n x)
  right-distributive-multiple-add-Euclidean-Domain =
    right-distributive-multiple-add-Integral-Domain
      ( integral-domain-Euclidean-Domain R)
```
