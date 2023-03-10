# The binomial theorem for rings

```agda
module ring-theory.binomial-theorem-rings where
```

<details><summary>Imports</summary>

```agda
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

open import linear-algebra.vectors-on-rings

open import ring-theory.binomial-theorem-semirings
open import ring-theory.powers-of-elements-rings
open import ring-theory.rings
open import ring-theory.sums-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem for rings asserts that for any two elements `x` and `y` of a commutative ring `R` and any natural number `n`, if `xy ＝ yx` holds then we have

```md
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

## Definitions

### Binomial sums

```agda
binomial-sum-Ring :
  {l : Level} (R : Ring l)
  (n : ℕ) (f : functional-vec-Ring R (succ-ℕ n)) → type-Ring R
binomial-sum-Ring R = binomial-sum-Semiring (semiring-Ring R)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  binomial-sum-one-element-Ring :
    (f : functional-vec-Ring R 1) →
    binomial-sum-Ring R 0 f ＝ head-functional-vec-Ring R 0 f
  binomial-sum-one-element-Ring =
    binomial-sum-one-element-Semiring (semiring-Ring R)

  binomial-sum-two-elements-Ring :
    (f : functional-vec-Ring R 2) →
    binomial-sum-Ring R 1 f ＝ add-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Ring =
    binomial-sum-two-elements-Semiring (semiring-Ring R)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-binomial-sum-Ring :
    (n : ℕ) {f g : functional-vec-Ring R (succ-ℕ n)} →
    (f ~ g) → binomial-sum-Ring R n f ＝ binomial-sum-Ring R n g
  htpy-binomial-sum-Ring = htpy-binomial-sum-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-binomial-sum-Ring :
    (n : ℕ) (x : type-Ring R) (f : functional-vec-Ring R (succ-ℕ n)) →
    mul-Ring R x (binomial-sum-Ring R n f) ＝
    binomial-sum-Ring R n (λ i → mul-Ring R x (f i))
  left-distributive-mul-binomial-sum-Ring =
    left-distributive-mul-binomial-sum-Semiring (semiring-Ring R)

  right-distributive-mul-binomial-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R (succ-ℕ n)) (x : type-Ring R) →
    mul-Ring R (binomial-sum-Ring R n f) x ＝
    binomial-sum-Ring R n (λ i → mul-Ring R (f i) x)
  right-distributive-mul-binomial-sum-Ring =
    right-distributive-mul-binomial-sum-Semiring (semiring-Ring R)
```

## Theorem

### Binomial theorem for rings

```agda
binomial-theorem-Ring :
  {l : Level} (R : Ring l) (n : ℕ) (x y : type-Ring R) →
  mul-Ring R x y ＝ mul-Ring R y x →
  power-Ring R n (add-Ring R x y) ＝
  binomial-sum-Ring R n
    ( λ i →
      mul-Ring R
      ( power-Ring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Ring R (dist-ℕ n (nat-Fin (succ-ℕ n) i)) y))
binomial-theorem-Ring R = binomial-theorem-Semiring (semiring-Ring R)
```
