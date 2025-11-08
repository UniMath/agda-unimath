# Powers of elements in large commutative rings

```agda
module commutative-algebra.powers-of-elements-large-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.large-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.large-monoids
open import group-theory.powers-of-elements-large-commutative-monoids
open import group-theory.powers-of-elements-large-monoids

open import ring-theory.large-rings
open import ring-theory.powers-of-elements-large-rings
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large commutative ring to a natural number power" Agda=power-Large-Commutative-Ring}}
on a [large commutative ring](ring-theory.large-rings.md) is the map `n x ↦ xⁿ`,
which is defined by [iteratively](foundation.iterating-functions.md) multiplying
`x` with itself `n` times.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  power-Large-Commutative-Ring :
    {l : Level} →
    ℕ → type-Large-Commutative-Ring R l → type-Large-Commutative-Ring R l
  power-Large-Commutative-Ring =
    power-Large-Ring (large-ring-Large-Commutative-Ring R)
```

## Properties

### The power operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    preserves-sim-power-Large-Commutative-Ring :
      {l1 l2 : Level} (n : ℕ) →
      (x : type-Large-Commutative-Ring R l1) →
      (y : type-Large-Commutative-Ring R l2) →
      sim-Large-Commutative-Ring R x y →
      sim-Large-Commutative-Ring R
        ( power-Large-Commutative-Ring R n x)
        ( power-Large-Commutative-Ring R n y)
    preserves-sim-power-Large-Commutative-Ring =
      preserves-sim-power-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
```

### `1ⁿ = 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    raise-power-one-Large-Commutative-Ring :
      (l : Level) (n : ℕ) →
      power-Large-Commutative-Ring R n (raise-one-Large-Commutative-Ring R l) ＝
      raise-one-Large-Commutative-Ring R l
    raise-power-one-Large-Commutative-Ring =
      raise-power-one-Large-Ring (large-ring-Large-Commutative-Ring R)

    power-one-Large-Commutative-Ring :
      (n : ℕ) →
      power-Large-Commutative-Ring R n (one-Large-Commutative-Ring R) ＝
      one-Large-Commutative-Ring R
    power-one-Large-Commutative-Ring =
      power-one-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    power-succ-Large-Commutative-Ring :
      {l : Level} (n : ℕ) (x : type-Large-Commutative-Ring R l) →
      power-Large-Commutative-Ring R (succ-ℕ n) x ＝
      mul-Large-Commutative-Ring R (power-Large-Commutative-Ring R n x) x
    power-succ-Large-Commutative-Ring =
      power-succ-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### `xⁿ⁺¹ = xxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    power-succ-Large-Commutative-Ring' :
      {l : Level} (n : ℕ) (x : type-Large-Commutative-Ring R l) →
      power-Large-Commutative-Ring R (succ-ℕ n) x ＝
      mul-Large-Commutative-Ring R x (power-Large-Commutative-Ring R n x)
    power-succ-Large-Commutative-Ring' =
      power-succ-Large-Ring' (large-ring-Large-Commutative-Ring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    distributive-power-add-Large-Commutative-Ring :
      {l : Level} (m n : ℕ) {x : type-Large-Commutative-Ring R l} →
      power-Large-Commutative-Ring R (m +ℕ n) x ＝
      mul-Large-Commutative-Ring R
        ( power-Large-Commutative-Ring R m x)
        ( power-Large-Commutative-Ring R n x)
    distributive-power-add-Large-Commutative-Ring =
      distributive-power-add-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    power-mul-Large-Commutative-Ring :
      {l : Level} (m n : ℕ) {x : type-Large-Commutative-Ring R l} →
      power-Large-Commutative-Ring R (m *ℕ n) x ＝
      power-Large-Commutative-Ring R n (power-Large-Commutative-Ring R m x)
    power-mul-Large-Commutative-Ring =
      power-mul-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### `(xy)ⁿ = xⁿyⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  abstract
    distributive-power-mul-Large-Commutative-Ring :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Commutative-Ring R l1} →
      {y : type-Large-Commutative-Ring R l2} →
      power-Large-Commutative-Ring R n (mul-Large-Commutative-Ring R x y) ＝
      mul-Large-Commutative-Ring R
        ( power-Large-Commutative-Ring R n x)
        ( power-Large-Commutative-Ring R n y)
    distributive-power-mul-Large-Commutative-Ring =
      distributive-power-mul-Large-Commutative-Monoid
        ( multiplicative-large-commutative-monoid-Large-Commutative-Ring R)
```
