# Powers of elements in commutative monoids

```agda
module group-theory.powers-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.powers-of-elements-monoids
```

</details>

The **power operation** on a [monoid](group-theory.monoids.md) is the map
`n x ↦ xⁿ`, which is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times.

## Definitions

### Powers of elements in commutative monoids

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  power-Commutative-Monoid :
    ℕ → type-Commutative-Monoid M → type-Commutative-Monoid M
  power-Commutative-Monoid = power-Monoid (monoid-Commutative-Monoid M)
```

### The predicate of being a power of an element in a commutative monoid

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-power-of-element-prop-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) → Prop l
  is-power-of-element-prop-Commutative-Monoid =
    is-power-of-element-prop-Monoid (monoid-Commutative-Monoid M)

  is-power-of-element-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) → UU l
  is-power-of-element-Commutative-Monoid =
    is-power-of-element-Monoid (monoid-Commutative-Monoid M)

  is-prop-is-power-of-element-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    is-prop (is-power-of-element-Commutative-Monoid x y)
  is-prop-is-power-of-element-Commutative-Monoid =
    is-prop-is-power-of-element-Monoid (monoid-Commutative-Monoid M)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  power-unit-Commutative-Monoid :
    (n : ℕ) →
    power-Commutative-Monoid M n (unit-Commutative-Monoid M) ＝
    unit-Commutative-Monoid M
  power-unit-Commutative-Monoid zero-ℕ = refl
  power-unit-Commutative-Monoid (succ-ℕ zero-ℕ) = refl
  power-unit-Commutative-Monoid (succ-ℕ (succ-ℕ n)) =
    right-unit-law-mul-Commutative-Monoid M _ ∙
    power-unit-Commutative-Monoid (succ-ℕ n)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  power-succ-Commutative-Monoid :
    (n : ℕ) (x : type-Commutative-Monoid M) →
    power-Commutative-Monoid M (succ-ℕ n) x ＝
    mul-Commutative-Monoid M (power-Commutative-Monoid M n x) x
  power-succ-Commutative-Monoid =
    power-succ-Monoid (monoid-Commutative-Monoid M)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  power-succ-Commutative-Monoid' :
    (n : ℕ) (x : type-Commutative-Monoid M) →
    power-Commutative-Monoid M (succ-ℕ n) x ＝
    mul-Commutative-Monoid M x (power-Commutative-Monoid M n x)
  power-succ-Commutative-Monoid' =
    power-succ-Monoid' (monoid-Commutative-Monoid M)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  distributive-power-add-Commutative-Monoid :
    (m n : ℕ) {x : type-Commutative-Monoid M} →
    power-Commutative-Monoid M (m +ℕ n) x ＝
    mul-Commutative-Monoid M
      ( power-Commutative-Monoid M m x)
      ( power-Commutative-Monoid M n x)
  distributive-power-add-Commutative-Monoid =
    distributive-power-add-Monoid (monoid-Commutative-Monoid M)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  distributive-power-mul-Commutative-Monoid :
    (n : ℕ) {x y : type-Commutative-Monoid M} →
    power-Commutative-Monoid M n (mul-Commutative-Monoid M x y) ＝
    mul-Commutative-Monoid M
      ( power-Commutative-Monoid M n x)
      ( power-Commutative-Monoid M n y)
  distributive-power-mul-Commutative-Monoid n =
    distributive-power-mul-Monoid
      ( monoid-Commutative-Monoid M)
      ( n)
      ( commutative-mul-Commutative-Monoid M _ _)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  power-mul-Commutative-Monoid :
    (m n : ℕ) {x : type-Commutative-Monoid M} →
    power-Commutative-Monoid M (m *ℕ n) x ＝
    power-Commutative-Monoid M n (power-Commutative-Monoid M m x)
  power-mul-Commutative-Monoid =
    power-mul-Monoid (monoid-Commutative-Monoid M)
```

### Commutative-Monoid homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (N : Commutative-Monoid l2) (f : hom-Commutative-Monoid M N)
  where

  preserves-powers-hom-Commutative-Monoid :
    (n : ℕ) (x : type-Commutative-Monoid M) →
    map-hom-Commutative-Monoid M N f (power-Commutative-Monoid M n x) ＝
    power-Commutative-Monoid N n (map-hom-Commutative-Monoid M N f x)
  preserves-powers-hom-Commutative-Monoid =
    preserves-powers-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)
```
