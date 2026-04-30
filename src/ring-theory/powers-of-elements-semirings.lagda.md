# Powers of elements in semirings

```agda
module ring-theory.powers-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.powers-of-elements-monoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.semirings
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="on a semiring" Agda=power-Semiring}}
on a [semiring](ring-theory.semirings.md) is the map `n x ↦ xⁿ`, which is
defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Semiring :
  {l : Level} (R : Semiring l) → ℕ → type-Semiring R → type-Semiring R
power-Semiring R n x = power-Monoid (multiplicative-monoid-Semiring R) n x
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  power-one-Semiring :
    (n : ℕ) → power-Semiring R n (one-Semiring R) ＝ one-Semiring R
  power-one-Semiring = power-unit-Monoid (multiplicative-monoid-Semiring R)
```

### `0ⁿ⁺¹ ＝ 0`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  power-zero-succ-Semiring :
    (n : ℕ) → power-Semiring R (succ-ℕ n) (zero-Semiring R) ＝ zero-Semiring R
  power-zero-succ-Semiring zero-ℕ = refl
  power-zero-succ-Semiring (succ-ℕ n) =
    right-zero-law-mul-Semiring R
      ( power-Semiring R (succ-ℕ n) (zero-Semiring R))
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  successor-law-power-Semiring :
    (n : ℕ) (x : type-Semiring R) →
    power-Semiring R (succ-ℕ n) x ＝ mul-Semiring R (power-Semiring R n x) x
  successor-law-power-Semiring = successor-law-power-Monoid (multiplicative-monoid-Semiring R)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  successor-law-power-Semiring' :
    (n : ℕ) (x : type-Semiring R) →
    power-Semiring R (succ-ℕ n) x ＝ mul-Semiring R x (power-Semiring R n x)
  successor-law-power-Semiring' = successor-law-power-Monoid' (multiplicative-monoid-Semiring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  distributive-power-add-Semiring :
    (m n : ℕ) {x : type-Semiring R} →
    power-Semiring R (m +ℕ n) x ＝
    mul-Semiring R (power-Semiring R m x) (power-Semiring R n x)
  distributive-power-add-Semiring =
    distributive-power-add-Monoid (multiplicative-monoid-Semiring R)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commute-powers-Semiring' :
    (n : ℕ) {x y : type-Semiring R} →
    ( mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R (power-Semiring R n x) y) ＝
    ( mul-Semiring R y (power-Semiring R n x))
  commute-powers-Semiring' =
    commute-powers-Monoid' (multiplicative-monoid-Semiring R)

  commute-powers-Semiring :
    (m n : ℕ) {x y : type-Semiring R} →
    ( mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R
      ( power-Semiring R m x)
      ( power-Semiring R n y)) ＝
    ( mul-Semiring R
      ( power-Semiring R n y)
      ( power-Semiring R m x))
  commute-powers-Semiring =
    commute-powers-Monoid (multiplicative-monoid-Semiring R)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  distributive-power-mul-Semiring :
    (n : ℕ) {x y : type-Semiring R} →
    (H : mul-Semiring R x y ＝ mul-Semiring R y x) →
    power-Semiring R n (mul-Semiring R x y) ＝
    mul-Semiring R (power-Semiring R n x) (power-Semiring R n y)
  distributive-power-mul-Semiring =
    distributive-power-mul-Monoid (multiplicative-monoid-Semiring R)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  power-mul-Semiring :
    (m n : ℕ) {x : type-Semiring R} →
    power-Semiring R (m *ℕ n) x ＝ power-Semiring R n (power-Semiring R m x)
  power-mul-Semiring = power-mul-Monoid (multiplicative-monoid-Semiring R)
```

### Homomorphisms of semirings preserve powers

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-power-hom-Semiring :
    (n : ℕ) {x : type-Semiring R} →
    map-hom-Semiring R S f (power-Semiring R n x) ＝
    power-Semiring S n (map-hom-Semiring R S f x)
  preserves-power-hom-Semiring =
    preserves-power-hom-Monoid
      ( multiplicative-monoid-Semiring R)
      ( multiplicative-monoid-Semiring S)
      ( hom-multiplicative-monoid-hom-Semiring R S f)
```
