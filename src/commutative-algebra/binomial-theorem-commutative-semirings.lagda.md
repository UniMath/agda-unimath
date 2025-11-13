# The binomial theorem in commutative semirings

```agda
module commutative-algebra.binomial-theorem-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.multiples-of-elements-commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-semirings

open import ring-theory.binomial-theorem-semirings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **binomial theorem** in commutative semirings asserts that for any two
elements `x` and `y` of a commutative semiring `A` and any natural number `n`,
we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-fin-sequence-type-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)) →
  type-Commutative-Semiring A
binomial-sum-fin-sequence-type-Commutative-Semiring A =
  binomial-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  binomial-sum-one-element-Commutative-Semiring :
    (f : fin-sequence-type-Commutative-Semiring A 1) →
    binomial-sum-fin-sequence-type-Commutative-Semiring A 0 f ＝
    head-fin-sequence-type-Commutative-Semiring A 0 f
  binomial-sum-one-element-Commutative-Semiring =
    binomial-sum-one-element-Semiring (semiring-Commutative-Semiring A)

  binomial-sum-two-elements-Commutative-Semiring :
    (f : fin-sequence-type-Commutative-Semiring A 2) →
    binomial-sum-fin-sequence-type-Commutative-Semiring A 1 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Semiring =
    binomial-sum-two-elements-Semiring (semiring-Commutative-Semiring A)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  htpy-binomial-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-fin-sequence-type-Commutative-Semiring A n f ＝
    binomial-sum-fin-sequence-type-Commutative-Semiring A n g
  htpy-binomial-sum-fin-sequence-type-Commutative-Semiring =
    htpy-binomial-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A)
    (f : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)) →
    mul-Commutative-Semiring A
      ( x)
      ( binomial-sum-fin-sequence-type-Commutative-Semiring A n f) ＝
    binomial-sum-fin-sequence-type-Commutative-Semiring A n
      ( λ i → mul-Commutative-Semiring A x (f i))
  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring =
    left-distributive-mul-binomial-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring A)

  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)) →
    (x : type-Commutative-Semiring A) →
    mul-Commutative-Semiring A
      ( binomial-sum-fin-sequence-type-Commutative-Semiring A n f)
      ( x) ＝
    binomial-sum-fin-sequence-type-Commutative-Semiring A n
      ( mul-Commutative-Semiring' A x ∘ f)
  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring =
    right-distributive-mul-binomial-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring A)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) →
  (n : ℕ) (x y : type-Commutative-Semiring A) →
  power-Commutative-Semiring A n (add-Commutative-Semiring A x y) ＝
  binomial-sum-fin-sequence-type-Commutative-Semiring A n
    ( λ i →
      mul-Commutative-Semiring A
      ( power-Commutative-Semiring A (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Semiring A (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Commutative-Semiring A n x y =
  binomial-theorem-Semiring
    ( semiring-Commutative-Semiring A)
    ( n)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Semiring A x y)
```

## Corollaries

### Computing `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n m : ℕ)
  (x y : type-Commutative-Semiring A) →
  power-Commutative-Semiring A (n +ℕ m) (add-Commutative-Semiring A x y) ＝
  add-Commutative-Semiring A
    ( mul-Commutative-Semiring A
      ( power-Commutative-Semiring A m y)
      ( sum-fin-sequence-type-Commutative-Semiring A n
        ( λ i →
          multiple-Commutative-Semiring A
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Commutative-Semiring A
              ( power-Commutative-Semiring A (nat-Fin n i) x)
              ( power-Commutative-Semiring A (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Commutative-Semiring A
      ( power-Commutative-Semiring A n x)
      ( sum-fin-sequence-type-Commutative-Semiring A
        ( succ-ℕ m)
        ( λ i →
          multiple-Commutative-Semiring A
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Commutative-Semiring A
              ( power-Commutative-Semiring A (nat-Fin (succ-ℕ m) i) x)
              ( power-Commutative-Semiring A
                ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                ( y))))))
is-linear-combination-power-add-Commutative-Semiring A n m x y =
  is-linear-combination-power-add-Semiring
    ( semiring-Commutative-Semiring A)
    ( n)
    ( m)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Semiring A x y)
```

## References

{{#bibliography}}
