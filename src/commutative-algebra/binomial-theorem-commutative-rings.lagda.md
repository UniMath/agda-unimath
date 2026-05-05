# The binomial theorem in commutative rings

```agda
module commutative-algebra.binomial-theorem-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-semirings
open import commutative-algebra.commutative-rings
open import commutative-algebra.multiples-of-elements-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-rings

open import ring-theory.binomial-theorem-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **binomial theorem** in commutative rings asserts that for any two elements
`x` and `y` of a commutative ring `A` and any natural number `n`, we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-fin-sequence-type-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l)
  (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
  type-Commutative-Ring A
binomial-sum-fin-sequence-type-Commutative-Ring A =
  binomial-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  binomial-sum-one-element-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 1) →
    binomial-sum-fin-sequence-type-Commutative-Ring A 0 f ＝
    head-fin-sequence-type-Commutative-Ring A 0 f
  binomial-sum-one-element-Commutative-Ring =
    binomial-sum-one-element-Ring (ring-Commutative-Ring A)

  binomial-sum-two-elements-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 2) →
    binomial-sum-fin-sequence-type-Commutative-Ring A 1 f ＝
    add-Commutative-Ring A (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Ring =
    binomial-sum-two-elements-Ring (ring-Commutative-Ring A)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  htpy-binomial-sum-fin-sequence-type-Commutative-Ring :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Ring A (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-fin-sequence-type-Commutative-Ring A n f ＝
    binomial-sum-fin-sequence-type-Commutative-Ring A n g
  htpy-binomial-sum-fin-sequence-type-Commutative-Ring =
    htpy-binomial-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A)
    (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
    mul-Commutative-Ring A
      ( x)
      ( binomial-sum-fin-sequence-type-Commutative-Ring A n f) ＝
    binomial-sum-fin-sequence-type-Commutative-Ring A
      ( n)
      ( mul-Commutative-Ring A x ∘ f)
  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring =
    left-distributive-mul-binomial-sum-fin-sequence-type-Ring
      ( ring-Commutative-Ring A)

  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
    (x : type-Commutative-Ring A) →
    mul-Commutative-Ring A
      ( binomial-sum-fin-sequence-type-Commutative-Ring A n f)
      ( x) ＝
    binomial-sum-fin-sequence-type-Commutative-Ring A
      ( n)
      ( mul-Commutative-Ring' A x ∘ f)
  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring =
    right-distributive-mul-binomial-sum-fin-sequence-type-Ring
      ( ring-Commutative-Ring A)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  (n : ℕ) (x y : type-Commutative-Ring A) →
  power-Commutative-Ring A n (add-Commutative-Ring A x y) ＝
  binomial-sum-fin-sequence-type-Commutative-Ring A n
    ( λ i →
      mul-Commutative-Ring A
      ( power-Commutative-Ring A (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Ring A (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Commutative-Ring A n x y =
  binomial-theorem-Ring
    ( ring-Commutative-Ring A)
    ( n)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Ring A x y)
```

## Corollaries

### Computing `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) (n m : ℕ)
  (x y : type-Commutative-Ring A) →
  power-Commutative-Ring A (n +ℕ m) (add-Commutative-Ring A x y) ＝
  add-Commutative-Ring A
    ( mul-Commutative-Ring A
      ( power-Commutative-Ring A m y)
      ( sum-fin-sequence-type-Commutative-Ring A n
        ( λ i →
          multiple-Commutative-Ring A
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Commutative-Ring A
              ( power-Commutative-Ring A (nat-Fin n i) x)
              ( power-Commutative-Ring A (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Commutative-Ring A
      ( power-Commutative-Ring A n x)
      ( sum-fin-sequence-type-Commutative-Ring A
        ( succ-ℕ m)
        ( λ i →
          multiple-Commutative-Ring A
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Commutative-Ring A
              ( power-Commutative-Ring A (nat-Fin (succ-ℕ m) i) x)
              ( power-Commutative-Ring A
                ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                ( y))))))
is-linear-combination-power-add-Commutative-Ring A =
  is-linear-combination-power-add-Commutative-Semiring
    ( commutative-semiring-Commutative-Ring A)
```

## References

{{#bibliography}}
