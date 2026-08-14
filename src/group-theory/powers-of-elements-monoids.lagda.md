# Powers of elements in monoids

```agda
module group-theory.powers-of-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.powers-of-elements-semigroups
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="monoid" Agda=power-Monoid}} on a [monoid](group-theory.monoids.md) is the map
`n x ↦ xⁿ`, which is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times.

We define the power operation such that the following equalities hold by definition:

```text
  x⁰ ≐ 1
  x¹ ≐ x
  xⁿ⁺² ≐ xⁿ⁺¹ · x.
```

This setup requires one extra step for the most basic properties, but it avoids having a superficial factor of the multiplicative unit in its definition for `n ≥ 1`.

## Definitions

### Powers of elements of monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-Monoid :
    ℕ → type-Monoid M → type-Monoid M
  power-Monoid zero-ℕ x =
    unit-Monoid M
  power-Monoid (succ-ℕ n) x =
    power-Semigroup (semigroup-Monoid M) (nonzero-succ-ℕ n) x
```

### The predicate of being a power of an element of a monoid

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-power-of-element-prop-Monoid : (x y : type-Monoid M) → Prop l
  is-power-of-element-prop-Monoid x y =
    exists-structure-Prop ℕ (λ n → power-Monoid M n x ＝ y)

  is-power-of-element-Monoid : (x y : type-Monoid M) → UU l
  is-power-of-element-Monoid x y =
    type-Prop (is-power-of-element-prop-Monoid x y)

  is-prop-is-power-of-element-Monoid :
    (x y : type-Monoid M) → is-prop (is-power-of-element-Monoid x y)
  is-prop-is-power-of-element-Monoid x y =
    is-prop-type-Prop (is-power-of-element-prop-Monoid x y)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    power-unit-Monoid :
      (n : ℕ) →
      power-Monoid M n (unit-Monoid M) ＝ unit-Monoid M
    power-unit-Monoid zero-ℕ = refl
    power-unit-Monoid (succ-ℕ zero-ℕ) = refl
    power-unit-Monoid (succ-ℕ (succ-ℕ n)) =
      right-unit-law-mul-Monoid M _ ∙ power-unit-Monoid (succ-ℕ n)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    successor-law-power-Monoid :
      (n : ℕ) (x : type-Monoid M) →
      power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M (power-Monoid M n x) x
    successor-law-power-Monoid zero-ℕ x = inv (left-unit-law-mul-Monoid M x)
    successor-law-power-Monoid (succ-ℕ n) x =
      successor-law-power-Semigroup (semigroup-Monoid M) (nonzero-succ-ℕ n) x
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    successor-law-power-Monoid' :
      (n : ℕ) (x : type-Monoid M) →
      power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M x (power-Monoid M n x)
    successor-law-power-Monoid' zero-ℕ x = inv (right-unit-law-mul-Monoid M x)
    successor-law-power-Monoid' (succ-ℕ n) x =
      successor-law-power-Semigroup' (semigroup-Monoid M) (nonzero-succ-ℕ n) x
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    distributive-power-add-Monoid :
      (m n : ℕ) {x : type-Monoid M} →
      power-Monoid M (m +ℕ n) x ＝
      mul-Monoid M (power-Monoid M m x) (power-Monoid M n x)
    distributive-power-add-Monoid m zero-ℕ =
      inv (right-unit-law-mul-Monoid M (power-Monoid M m _))
    distributive-power-add-Monoid zero-ℕ (succ-ℕ n) {x} =
      ap (λ t → power-Monoid M t x) (left-unit-law-add-ℕ (succ-ℕ n)) ∙
      inv (left-unit-law-mul-Monoid M (power-Monoid M (succ-ℕ n) _))
    distributive-power-add-Monoid (succ-ℕ m) (succ-ℕ n) =
      distributive-power-add-Semigroup
        ( semigroup-Monoid M)
        ( nonzero-succ-ℕ m)
        ( nonzero-succ-ℕ n)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    commute-powers-Monoid' :
      (n : ℕ) {x y : type-Monoid M} →
      mul-Monoid M x y ＝ mul-Monoid M y x →
      mul-Monoid M (power-Monoid M n x) y ＝ mul-Monoid M y (power-Monoid M n x)
    commute-powers-Monoid' zero-ℕ H =
      left-unit-law-mul-Monoid M _ ∙ inv (right-unit-law-mul-Monoid M _)
    commute-powers-Monoid' (succ-ℕ n) =
      commute-powers-Semigroup' (semigroup-Monoid M) (nonzero-succ-ℕ n)

    commute-powers-Monoid :
      (m n : ℕ) {x y : type-Monoid M} →
      mul-Monoid M x y ＝ mul-Monoid M y x →
      mul-Monoid M (power-Monoid M m x) (power-Monoid M n y) ＝
      mul-Monoid M (power-Monoid M n y) (power-Monoid M m x)
    commute-powers-Monoid m n p =
      inv (commute-powers-Monoid' n (inv (commute-powers-Monoid' m p)))
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    distributive-power-mul-Monoid :
      (n : ℕ) {x y : type-Monoid M} →
      (H : mul-Monoid M x y ＝ mul-Monoid M y x) →
      power-Monoid M n (mul-Monoid M x y) ＝
      mul-Monoid M (power-Monoid M n x) (power-Monoid M n y)
    distributive-power-mul-Monoid zero-ℕ H =
      inv (left-unit-law-mul-Monoid M (unit-Monoid M))
    distributive-power-mul-Monoid (succ-ℕ n) H =
      distributive-power-mul-Semigroup (semigroup-Monoid M) (nonzero-succ-ℕ n) H
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    power-mul-Monoid :
      (m n : ℕ) {x : type-Monoid M} →
      power-Monoid M (m *ℕ n) x ＝
      power-Monoid M n (power-Monoid M m x)
    power-mul-Monoid zero-ℕ n {x} =
      inv (power-unit-Monoid M n)
    power-mul-Monoid (succ-ℕ m) zero-ℕ {x} =
      ap (λ t → power-Monoid M t x) (right-zero-law-mul-ℕ m)
    power-mul-Monoid (succ-ℕ m) (succ-ℕ n) =
      power-mul-Semigroup
        ( semigroup-Monoid M)
        ( nonzero-succ-ℕ m)
        ( nonzero-succ-ℕ n)
```

### Monoid homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  abstract
    preserves-power-hom-Monoid :
      (n : ℕ) {x : type-Monoid M} →
      map-hom-Monoid M N f (power-Monoid M n x) ＝
      power-Monoid N n (map-hom-Monoid M N f x)
    preserves-power-hom-Monoid zero-ℕ = preserves-unit-hom-Monoid M N f
    preserves-power-hom-Monoid (succ-ℕ n) =
      preserves-power-hom-Semigroup
        ( semigroup-Monoid M)
        ( semigroup-Monoid N)
        ( hom-semigroup-hom-Monoid M N f)
        ( nonzero-succ-ℕ n)
```
