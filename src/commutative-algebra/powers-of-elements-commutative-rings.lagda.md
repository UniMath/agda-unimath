# Powers of elements in commutative rings

```agda
module commutative-algebra.powers-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
```

</details>

## Idea

The **power operation** on a commutative ring is the map `n x ↦ xⁿ`, which is
defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  ℕ → type-Commutative-Ring A → type-Commutative-Ring A
power-Commutative-Ring A = power-Ring (ring-Commutative-Ring A)
```

## Properties

### `xⁿ⁺¹ = xⁿx` and `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-succ-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A (succ-ℕ n) x ＝
    mul-Commutative-Ring A (power-Commutative-Ring A n x) x
  power-succ-Commutative-Ring =
    power-succ-Ring (ring-Commutative-Ring A)

  power-succ-Commutative-Ring' :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A (succ-ℕ n) x ＝
    mul-Commutative-Ring A x (power-Commutative-Ring A n x)
  power-succ-Commutative-Ring' =
    power-succ-Ring' (ring-Commutative-Ring A)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  distributive-power-add-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    power-Commutative-Ring A (m +ℕ n) x ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A m x)
      ( power-Commutative-Ring A n x)
  distributive-power-add-Commutative-Ring =
    distributive-power-add-Ring (ring-Commutative-Ring A)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-mul-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring A} →
    power-Commutative-Ring A (m *ℕ n) x ＝
    power-Commutative-Ring A n (power-Commutative-Ring A m x)
  power-mul-Commutative-Ring =
    power-mul-Ring (ring-Commutative-Ring A)
```

### Powers distribute over multiplication

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  distributive-power-mul-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring A) →
    power-Commutative-Ring A n (mul-Commutative-Ring A x y) ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A n x)
      ( power-Commutative-Ring A n y)
  distributive-power-mul-Commutative-Ring n x y =
    distributive-power-mul-Ring
      ( ring-Commutative-Ring A)
      ( n)
      ( commutative-mul-Commutative-Ring A x y)
```

### `(-x)ⁿ = (-1)ⁿxⁿ`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    mul-Commutative-Ring A
      ( power-Commutative-Ring A n (neg-one-Commutative-Ring A))
      ( power-Commutative-Ring A n x)
  power-neg-Commutative-Ring =
    power-neg-Ring (ring-Commutative-Ring A)

  even-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    is-even-ℕ n →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    power-Commutative-Ring A n x
  even-power-neg-Commutative-Ring =
    even-power-neg-Ring (ring-Commutative-Ring A)

  odd-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    is-odd-ℕ n →
    power-Commutative-Ring A n (neg-Commutative-Ring A x) ＝
    neg-Commutative-Ring A (power-Commutative-Ring A n x)
  odd-power-neg-Commutative-Ring =
    odd-power-neg-Ring (ring-Commutative-Ring A)
```

### Commutative ring homomorphisms preserve powers of elements

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : Commutative-Ring l2)
  (f : hom-Commutative-Ring R S)
  where

  abstract
    preserves-powers-hom-Commutative-Ring :
      (n : ℕ) (x : type-Commutative-Ring R) →
      map-hom-Commutative-Ring R S f (power-Commutative-Ring R n x) ＝
      power-Commutative-Ring S n (map-hom-Commutative-Ring R S f x)
    preserves-powers-hom-Commutative-Ring =
      preserves-powers-hom-Ring
        ( ring-Commutative-Ring R)
        ( ring-Commutative-Ring S)
        ( f)
```
