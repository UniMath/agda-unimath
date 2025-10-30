# The binomial theorem for rings

```agda
module ring-theory.binomial-theorem-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings

open import ring-theory.binomial-theorem-semirings
open import ring-theory.powers-of-elements-rings
open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "binomial theorem" Disambiguation="for rings" WD="binomial theorem" WDID=Q26708 Agda=binomial-theorem-Ring}}
for [rings](ring-theory.rings.md) asserts that for any two elements `x` and `y`
of a ring `R` such that `xy = yx` and any
[natural number](elementary-number-theory.natural-numbers.md) `n` we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-fin-sequence-type-Ring :
  {l : Level} (R : Ring l)
  (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) → type-Ring R
binomial-sum-fin-sequence-type-Ring R =
  binomial-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  binomial-sum-one-element-Ring :
    (f : fin-sequence-type-Ring R 1) →
    binomial-sum-fin-sequence-type-Ring R 0 f ＝
    head-fin-sequence-type-Ring R 0 f
  binomial-sum-one-element-Ring =
    binomial-sum-one-element-Semiring (semiring-Ring R)

  binomial-sum-two-elements-Ring :
    (f : fin-sequence-type-Ring R 2) →
    binomial-sum-fin-sequence-type-Ring R 1 f ＝
    add-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Ring =
    binomial-sum-two-elements-Semiring (semiring-Ring R)
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-binomial-sum-fin-sequence-type-Ring :
    (n : ℕ) {f g : fin-sequence-type-Ring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-fin-sequence-type-Ring R n f ＝
    binomial-sum-fin-sequence-type-Ring R n g
  htpy-binomial-sum-fin-sequence-type-Ring =
    htpy-binomial-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-binomial-sum-fin-sequence-type-Ring :
    (n : ℕ) (x : type-Ring R) (f : fin-sequence-type-Ring R (succ-ℕ n)) →
    mul-Ring R x (binomial-sum-fin-sequence-type-Ring R n f) ＝
    binomial-sum-fin-sequence-type-Ring R n (λ i → mul-Ring R x (f i))
  left-distributive-mul-binomial-sum-fin-sequence-type-Ring =
    left-distributive-mul-binomial-sum-fin-sequence-type-Semiring
      ( semiring-Ring R)

  right-distributive-mul-binomial-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) (x : type-Ring R) →
    mul-Ring R (binomial-sum-fin-sequence-type-Ring R n f) x ＝
    binomial-sum-fin-sequence-type-Ring R n (λ i → mul-Ring R (f i) x)
  right-distributive-mul-binomial-sum-fin-sequence-type-Ring =
    right-distributive-mul-binomial-sum-fin-sequence-type-Semiring
      ( semiring-Ring R)
```

## Theorem

### Binomial theorem for rings

```agda
binomial-theorem-Ring :
  {l : Level} (R : Ring l) (n : ℕ) (x y : type-Ring R) →
  mul-Ring R x y ＝ mul-Ring R y x →
  power-Ring R n (add-Ring R x y) ＝
  binomial-sum-fin-sequence-type-Ring R n
    ( λ i →
      mul-Ring R
      ( power-Ring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Ring R (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Ring R = binomial-theorem-Semiring (semiring-Ring R)
```

## Corollaries

### If `x` commutes with `y`, then we can compute `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Ring :
  {l : Level} (R : Ring l) (n m : ℕ) (x y : type-Ring R) →
  mul-Ring R x y ＝ mul-Ring R y x →
  power-Ring R (n +ℕ m) (add-Ring R x y) ＝
  add-Ring R
    ( mul-Ring R
      ( power-Ring R m y)
      ( sum-fin-sequence-type-Ring R n
        ( λ i →
          mul-nat-scalar-Ring R
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Ring R
              ( power-Ring R (nat-Fin n i) x)
              ( power-Ring R (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Ring R
      ( power-Ring R n x)
      ( sum-fin-sequence-type-Ring R
        ( succ-ℕ m)
        ( λ i →
          mul-nat-scalar-Ring R
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Ring R
              ( power-Ring R (nat-Fin (succ-ℕ m) i) x)
              ( power-Ring R (dist-ℕ (nat-Fin (succ-ℕ m) i) m) y)))))
is-linear-combination-power-add-Ring R =
  is-linear-combination-power-add-Semiring (semiring-Ring R)
```

## References

{{#bibliography}}
