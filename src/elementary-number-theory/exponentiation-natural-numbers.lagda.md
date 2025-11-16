# Exponentiation of natural numbers

```agda
module elementary-number-theory.exponentiation-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.semiring-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The {{#concept "exponent" Agda=exp-ℕ WD="exponentiation" WDID=Q33456}} $m^n$ of
two [natural numbers](elementary-number-theory.natural-numbers.md) is the number
obtained by multiplying $m$ with itself $n$ times.

## Definition

```agda
exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ m 0 = 1
exp-ℕ m (succ-ℕ n) = (exp-ℕ m n) *ℕ m

infixr 45 _^ℕ_
_^ℕ_ = exp-ℕ
```

```agda
power-ℕ : ℕ → ℕ → ℕ
power-ℕ = power-Commutative-Semiring ℕ-Commutative-Semiring
```

## Properties

These properties are the axioms associated with
[Tarski's high school algebra problem](https://en.wikipedia.org/wiki/Tarski%27s_high_school_algebra_problem).

### 1^n = 1 for all n

```agda
abstract
  annihilation-law-exp-ℕ : (n : ℕ) → 1 ^ℕ n ＝ 1
  annihilation-law-exp-ℕ zero-ℕ = refl
  annihilation-law-exp-ℕ (succ-ℕ n) =
    right-unit-law-mul-ℕ (1 ^ℕ n) ∙ annihilation-law-exp-ℕ n
```

### `xʸ⁺ᶻ = xʸ xᶻ`

```agda
abstract
  left-distributive-exp-add-ℕ :
    (x y z : ℕ) → x ^ℕ (y +ℕ z) ＝ (x ^ℕ y) *ℕ (x ^ℕ z)
  left-distributive-exp-add-ℕ x y zero-ℕ = inv (right-unit-law-mul-ℕ (x ^ℕ y))
  left-distributive-exp-add-ℕ x y (succ-ℕ z) =
    ( ap (_*ℕ x) (left-distributive-exp-add-ℕ x y z)) ∙
    ( associative-mul-ℕ (x ^ℕ y) (x ^ℕ z) x)
```

### `(xy)ᶻ = xᶻ yᶻ`

```agda
abstract
  right-distributive-exp-mul-ℕ :
    (x y z : ℕ) → (x *ℕ y) ^ℕ z ＝ (x ^ℕ z) *ℕ (y ^ℕ z)
  right-distributive-exp-mul-ℕ x y zero-ℕ = refl
  right-distributive-exp-mul-ℕ x y (succ-ℕ z) =
    ( ap (_*ℕ (x *ℕ y)) (right-distributive-exp-mul-ℕ x y z)) ∙
    ( interchange-law-mul-mul-ℕ (x ^ℕ z) (y ^ℕ z) x y)
```

### `xʸᶻ = (xʸ)ᶻ`

```agda
abstract
  exp-mul-ℕ : (x y z : ℕ) → x ^ℕ (y *ℕ z) ＝ (x ^ℕ y) ^ℕ z
  exp-mul-ℕ x zero-ℕ z = inv (annihilation-law-exp-ℕ z)
  exp-mul-ℕ x (succ-ℕ y) z =
    ( left-distributive-exp-add-ℕ x (y *ℕ z) z) ∙
    ( ap (_*ℕ (x ^ℕ z)) (exp-mul-ℕ x y z)) ∙
    ( inv (right-distributive-exp-mul-ℕ (x ^ℕ y) x z))
```

### If `m` is nonzero, `mⁿ` is nonzero

```agda
abstract
  is-nonzero-exp-ℕ :
    (m n : ℕ) → is-nonzero-ℕ m → is-nonzero-ℕ (m ^ℕ n)
  is-nonzero-exp-ℕ m zero-ℕ p = is-nonzero-one-ℕ
  is-nonzero-exp-ℕ m (succ-ℕ n) p =
    is-nonzero-mul-ℕ (m ^ℕ n) m (is-nonzero-exp-ℕ m n p) p

exp-ℕ⁺ : ℕ⁺ → ℕ → ℕ⁺
exp-ℕ⁺ (n , n≠0) m = (exp-ℕ n m , is-nonzero-exp-ℕ n m n≠0)
```

### The exponent $m^n$ is equal to the $n$-fold product of $m$

```agda
compute-constant-product-ℕ :
  (m n : ℕ) → Π-ℕ n (λ _ → m) ＝ exp-ℕ m n
compute-constant-product-ℕ m zero-ℕ = refl
compute-constant-product-ℕ m (succ-ℕ n) =
  ap (_*ℕ m) (compute-constant-product-ℕ m n)
```
