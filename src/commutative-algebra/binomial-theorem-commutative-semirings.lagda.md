# The binomial theorem in commutative semirings

```agda
module commutative-algebra.binomial-theorem-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-commutative-semirings

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

open import linear-algebra.vectors-on-commutative-semirings

open import ring-theory.binomial-theorem-semirings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem in commutative semirings asserts that for any two elements `x` and `y` of a commutative semiring `R` and any natural number `n`, we have

```md
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l)
  (n : ℕ) (f : functional-vec-Commutative-Semiring R (succ-ℕ n)) →
  type-Commutative-Semiring R
binomial-sum-Commutative-Semiring R =
  binomial-sum-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  binomial-sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring R 1) →
    binomial-sum-Commutative-Semiring R 0 f ＝
    head-functional-vec-Commutative-Semiring R 0 f
  binomial-sum-one-element-Commutative-Semiring =
    binomial-sum-one-element-Semiring (semiring-Commutative-Semiring R)

  binomial-sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring R 2) →
    binomial-sum-Commutative-Semiring R 1 f ＝
    add-Commutative-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Semiring =
    binomial-sum-two-elements-Semiring (semiring-Commutative-Semiring R)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-binomial-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-vec-Commutative-Semiring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-Commutative-Semiring R n f ＝
    binomial-sum-Commutative-Semiring R n g
  htpy-binomial-sum-Commutative-Semiring =
    htpy-binomial-sum-Semiring (semiring-Commutative-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-distributive-mul-binomial-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring R)
    (f : functional-vec-Commutative-Semiring R (succ-ℕ n)) →
    mul-Commutative-Semiring R x (binomial-sum-Commutative-Semiring R n f) ＝
    binomial-sum-Commutative-Semiring R n
      ( λ i → mul-Commutative-Semiring R x (f i))
  left-distributive-mul-binomial-sum-Commutative-Semiring =
    left-distributive-mul-binomial-sum-Semiring
      ( semiring-Commutative-Semiring R)

  right-distributive-mul-binomial-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R (succ-ℕ n)) →
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (binomial-sum-Commutative-Semiring R n f) x ＝
    binomial-sum-Commutative-Semiring R n
      ( λ i → mul-Commutative-Semiring R (f i) x)
  right-distributive-mul-binomial-sum-Commutative-Semiring =
    right-distributive-mul-binomial-sum-Semiring
      ( semiring-Commutative-Semiring R)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) →
  (n : ℕ) (x y : type-Commutative-Semiring R) →
  power-Commutative-Semiring R n (add-Commutative-Semiring R x y) ＝
  binomial-sum-Commutative-Semiring R n
    ( λ i →
      mul-Commutative-Semiring R
      ( power-Commutative-Semiring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Semiring R (dist-ℕ n (nat-Fin (succ-ℕ n) i)) y))
binomial-theorem-Commutative-Semiring R n x y =
  binomial-theorem-Semiring
    ( semiring-Commutative-Semiring R)
    ( n)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Semiring R x y)
```
