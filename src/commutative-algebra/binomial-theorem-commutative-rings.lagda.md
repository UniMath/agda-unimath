# The binomial theorem in commutative rings

```agda
module commutative-algebra.binomial-theorem-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors-on-commutative-rings

open import ring-theory.binomial-theorem-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem in commutative rings asserts that for any two elements `x` and `y` of a commutative ring `R` and any natural number `n`, we have

```md
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
  type-Commutative-Ring R
binomial-sum-Commutative-Ring R = binomial-sum-Ring (ring-Commutative-Ring R)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  binomial-sum-one-element-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 1) →
    binomial-sum-Commutative-Ring R 0 f ＝
    head-functional-vec-Commutative-Ring R 0 f
  binomial-sum-one-element-Commutative-Ring =
    binomial-sum-one-element-Ring (ring-Commutative-Ring R)

  binomial-sum-two-elements-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 2) →
    binomial-sum-Commutative-Ring R 1 f ＝
    add-Commutative-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Ring =
    binomial-sum-two-elements-Ring (ring-Commutative-Ring R)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-binomial-sum-Commutative-Ring :
    (n : ℕ) {f g : functional-vec-Commutative-Ring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-Commutative-Ring R n f ＝ binomial-sum-Commutative-Ring R n g
  htpy-binomial-sum-Commutative-Ring =
    htpy-binomial-sum-Ring (ring-Commutative-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-binomial-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R)
    (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    mul-Commutative-Ring R x (binomial-sum-Commutative-Ring R n f) ＝
    binomial-sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R x (f i))
  left-distributive-mul-binomial-sum-Commutative-Ring =
    left-distributive-mul-binomial-sum-Ring (ring-Commutative-Ring R)

  right-distributive-mul-binomial-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (binomial-sum-Commutative-Ring R n f) x ＝
    binomial-sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R (f i) x)
  right-distributive-mul-binomial-sum-Commutative-Ring =
    right-distributive-mul-binomial-sum-Ring (ring-Commutative-Ring R)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  (n : ℕ) (x y : type-Commutative-Ring R) →
  power-Commutative-Ring R n (add-Commutative-Ring R x y) ＝
  binomial-sum-Commutative-Ring R n
    ( λ i →
      mul-Commutative-Ring R
      ( power-Commutative-Ring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Ring R (dist-ℕ n (nat-Fin (succ-ℕ n) i)) y))
binomial-theorem-Commutative-Ring R n x y =
  binomial-theorem-Ring
    ( ring-Commutative-Ring R)
    ( n)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Ring R x y)
```
