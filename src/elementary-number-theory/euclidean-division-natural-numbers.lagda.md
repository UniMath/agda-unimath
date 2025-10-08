# Euclidean division on the natural numbers

```agda
module elementary-number-theory.euclidean-division-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Euclidean division is division with remainder, i.e., the Euclidean division of
`n` by `d` is the largest natural number `k ≤ n/d`, and the remainder is the
unique natural number `r < d` such that `kd + r = n`.

## Definitions

### Euclidean division via an array of natural numbers

The following definition produces for each `k : ℕ` a sequence of sequences as
follows:

```text
    This is column k
      ↓
  0,…,0,0,0,0,0,0,0,…  -- The sequence at row 0 is the constant sequence
  1,0,…,0,0,0,0,0,0,…  -- We append 1's at the start
      ⋮
  1,…,1,0,…,0,0,0,0,…  -- This is row k+1
  2,1,…,1,0,0,0,0,0,…  -- After k+1 steps we append 2's at the start
      ⋮
  2,…,2,1,…,1,0,…,0,…  -- This is row 2(k+1)
  3,2,…,2,1,…,1,0,0,…  -- After another k+1 steps we append 3's at the start
      ⋮
```

This produces an array of natural numbers. We find the quotient of the euclidean
division of `n` by `k+1` in the `k`-th column of the `n`-th row of this array.
We will arbitrarily set the quotient of the euclidean division of `n` by `0` to
`0` in this definition.

```agda
array-quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ → ℕ
array-quotient-euclidean-division-ℕ k zero-ℕ m = zero-ℕ
array-quotient-euclidean-division-ℕ k (succ-ℕ n) zero-ℕ =
  succ-ℕ (array-quotient-euclidean-division-ℕ k n k)
array-quotient-euclidean-division-ℕ k (succ-ℕ n) (succ-ℕ m) =
  array-quotient-euclidean-division-ℕ k n m

quotient-euclidean-division-ℕ' : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ' zero-ℕ n = zero-ℕ
quotient-euclidean-division-ℕ' (succ-ℕ k) n =
  array-quotient-euclidean-division-ℕ k n k
```

### Euclidean division via modular arithmetic

```agda
euclidean-division-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ k x r) × (is-nonzero-ℕ k → le-ℕ r k))
pr1 (euclidean-division-ℕ zero-ℕ x) = x
pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)
pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
  symmetric-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)
pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
  strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)

remainder-euclidean-division-ℕ : ℕ → ℕ → ℕ
remainder-euclidean-division-ℕ k x =
  pr1 (euclidean-division-ℕ k x)

cong-euclidean-division-ℕ :
  (k x : ℕ) → cong-ℕ k x (remainder-euclidean-division-ℕ k x)
cong-euclidean-division-ℕ k x =
  pr1 (pr2 (euclidean-division-ℕ k x))

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → le-ℕ (remainder-euclidean-division-ℕ k x) k
strict-upper-bound-remainder-euclidean-division-ℕ k x =
  pr2 (pr2 (euclidean-division-ℕ k x))

quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ k x =
  pr1 (cong-euclidean-division-ℕ k x)

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) →
  ( (quotient-euclidean-division-ℕ k x) *ℕ k) ＝
  ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

eq-euclidean-division-ℕ :
  (k x : ℕ) →
  ( add-ℕ
    ( (quotient-euclidean-division-ℕ k x) *ℕ k)
    ( remainder-euclidean-division-ℕ k x)) ＝
  ( x)
eq-euclidean-division-ℕ zero-ℕ x =
  ( inv
    ( ap
      ( _+ℕ x)
      ( right-zero-law-mul-ℕ (quotient-euclidean-division-ℕ zero-ℕ x)))) ∙
  ( left-unit-law-add-ℕ x)
eq-euclidean-division-ℕ (succ-ℕ k) x =
  ( ap
    ( _+ℕ (remainder-euclidean-division-ℕ (succ-ℕ k) x))
    ( ( pr2 (cong-euclidean-division-ℕ (succ-ℕ k) x)) ∙
      ( commutative-dist-ℕ x
        ( remainder-euclidean-division-ℕ (succ-ℕ k) x)))) ∙
  ( is-difference-dist-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x) x
    ( leq-nat-mod-succ-ℕ k x))
```

```agda
map-extended-euclidean-algorithm : ℕ × ℕ → ℕ × ℕ
pr1 (map-extended-euclidean-algorithm (pair x y)) = y
pr2 (map-extended-euclidean-algorithm (pair x y)) =
  remainder-euclidean-division-ℕ y x
```
