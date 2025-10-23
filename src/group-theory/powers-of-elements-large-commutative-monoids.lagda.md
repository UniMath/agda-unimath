# Powers of elements in large commutative monoids

```agda
module group-theory.powers-of-elements-large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.powers-of-elements-large-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large commutative monoid to a natural number power" Agda=power-Large-Commutative-Monoid}}
on a [large commutative monoid](group-theory.large-commutative-monoids.md) is
inherited from the
[power operation](group-theory.powers-of-elements-large-monoids.md) on the
underlying [large monoid](group-theory.large-monoids.md).

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  power-Large-Commutative-Monoid :
    {l : Level} → ℕ → type-Large-Commutative-Monoid M l →
    type-Large-Commutative-Monoid M l
  power-Large-Commutative-Monoid =
    power-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

## Properties

### The power operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    preserves-sim-power-Large-Commutative-Monoid :
      {l1 l2 : Level} (n : ℕ) →
      (x : type-Large-Commutative-Monoid M l1) →
      (y : type-Large-Commutative-Monoid M l2) →
      sim-Large-Commutative-Monoid M x y →
      sim-Large-Commutative-Monoid M
        ( power-Large-Commutative-Monoid M n x)
        ( power-Large-Commutative-Monoid M n y)
    preserves-sim-power-Large-Commutative-Monoid =
      preserves-sim-power-Large-Monoid
        ( large-monoid-Large-Commutative-Monoid M)
```

### `1ⁿ = 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    raise-power-unit-Large-Commutative-Monoid :
      (l : Level) (n : ℕ) →
      power-Large-Commutative-Monoid M n
        ( raise-unit-Large-Commutative-Monoid M l) ＝
      raise-unit-Large-Commutative-Monoid M l
    raise-power-unit-Large-Commutative-Monoid =
      raise-power-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    power-succ-Large-Commutative-Monoid :
      {l : Level} (n : ℕ) (x : type-Large-Commutative-Monoid M l) →
      power-Large-Commutative-Monoid M (succ-ℕ n) x ＝
      mul-Large-Commutative-Monoid M (power-Large-Commutative-Monoid M n x) x
    power-succ-Large-Commutative-Monoid =
      power-succ-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### `xⁿ⁺¹ = xxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    power-succ-Large-Commutative-Monoid' :
      {l : Level} (n : ℕ) (x : type-Large-Commutative-Monoid M l) →
      power-Large-Commutative-Monoid M (succ-ℕ n) x ＝
      mul-Large-Commutative-Monoid M x (power-Large-Commutative-Monoid M n x)
    power-succ-Large-Commutative-Monoid' =
      power-succ-Large-Monoid' (large-monoid-Large-Commutative-Monoid M)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    distributive-power-add-Large-Commutative-Monoid :
      {l : Level} (m n : ℕ) {x : type-Large-Commutative-Monoid M l} →
      power-Large-Commutative-Monoid M (m +ℕ n) x ＝
      mul-Large-Commutative-Monoid M
        ( power-Large-Commutative-Monoid M m x)
        ( power-Large-Commutative-Monoid M n x)
    distributive-power-add-Large-Commutative-Monoid =
      distributive-power-add-Large-Monoid
        ( large-monoid-Large-Commutative-Monoid M)
```

### `(xy)ⁿ = xⁿyⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    distributive-power-mul-Large-Commutative-Monoid :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Commutative-Monoid M l1} →
      {y : type-Large-Commutative-Monoid M l2} →
      power-Large-Commutative-Monoid M n (mul-Large-Commutative-Monoid M x y) ＝
      mul-Large-Commutative-Monoid M
        ( power-Large-Commutative-Monoid M n x)
        ( power-Large-Commutative-Monoid M n y)
    distributive-power-mul-Large-Commutative-Monoid n =
      distributive-power-mul-Large-Monoid
        ( large-monoid-Large-Commutative-Monoid M)
        ( n)
        ( commutative-mul-Large-Commutative-Monoid M _ _)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    power-mul-Large-Commutative-Monoid :
      {l : Level} (m n : ℕ) {x : type-Large-Commutative-Monoid M l} →
      power-Large-Commutative-Monoid M (m *ℕ n) x ＝
      power-Large-Commutative-Monoid M n (power-Large-Commutative-Monoid M m x)
    power-mul-Large-Commutative-Monoid =
      power-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```
