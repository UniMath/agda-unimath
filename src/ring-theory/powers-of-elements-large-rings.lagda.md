# Powers of elements in large rings

```agda
module ring-theory.powers-of-elements-large-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.large-monoids
open import group-theory.powers-of-elements-large-monoids

open import ring-theory.large-rings
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large ring to a natural number power" Agda=power-Large-Ring}}
on a [large ring](ring-theory.large-rings.md) is the map `n x ↦ xⁿ`, which is
defined by [iteratively](foundation.iterating-functions.md) multiplying `x` with
itself `n` times.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  power-Large-Ring : {l : Level} → ℕ → type-Large-Ring R l → type-Large-Ring R l
  power-Large-Ring =
    power-Large-Monoid (multiplicative-large-monoid-Large-Ring R)
```

## Properties

### The power operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    preserves-sim-power-Large-Ring :
      {l1 l2 : Level} (n : ℕ) →
      (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      sim-Large-Ring R x y →
      sim-Large-Ring R (power-Large-Ring R n x) (power-Large-Ring R n y)
    preserves-sim-power-Large-Ring =
      preserves-sim-power-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)
```

### `1ⁿ = 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    raise-power-one-Large-Ring :
      (l : Level) (n : ℕ) →
      power-Large-Ring R n (raise-one-Large-Ring R l) ＝
      raise-one-Large-Ring R l
    raise-power-one-Large-Ring =
      raise-power-unit-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)

    power-one-Large-Ring :
      (n : ℕ) → power-Large-Ring R n (one-Large-Ring R) ＝ one-Large-Ring R
    power-one-Large-Ring =
      power-unit-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)
```

### For nonzero `n`, `0ⁿ = 0`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    power-nonzero-raise-zero-Large-Ring :
      (l : Level) (n : ℕ⁺) →
      power-Large-Ring R (nat-ℕ⁺ n) (raise-zero-Large-Ring R l) ＝
      raise-zero-Large-Ring R l
    power-nonzero-raise-zero-Large-Ring l (0 , H) = ex-falso (H refl)
    power-nonzero-raise-zero-Large-Ring l (1 , _) = refl
    power-nonzero-raise-zero-Large-Ring l (succ-ℕ n@(succ-ℕ _) , _) =
      right-raise-zero-law-mul-Large-Ring R l _

    power-nonzero-zero-Large-Ring :
      (n : ℕ⁺) →
      power-Large-Ring R (nat-ℕ⁺ n) (zero-Large-Ring R) ＝ zero-Large-Ring R
    power-nonzero-zero-Large-Ring n =
      ( ap
        ( power-Large-Ring R (nat-ℕ⁺ n))
        ( inv (eq-raise-Large-Ring R lzero (zero-Large-Ring R)))) ∙
      ( power-nonzero-raise-zero-Large-Ring lzero n) ∙
      ( eq-raise-Large-Ring R lzero (zero-Large-Ring R))
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    power-succ-Large-Ring :
      {l : Level} (n : ℕ) (x : type-Large-Ring R l) →
      power-Large-Ring R (succ-ℕ n) x ＝
      mul-Large-Ring R (power-Large-Ring R n x) x
    power-succ-Large-Ring =
      power-succ-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)
```

### `xⁿ⁺¹ = xxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    power-succ-Large-Ring' :
      {l : Level} (n : ℕ) (x : type-Large-Ring R l) →
      power-Large-Ring R (succ-ℕ n) x ＝
      mul-Large-Ring R x (power-Large-Ring R n x)
    power-succ-Large-Ring' =
      power-succ-Large-Monoid'
        ( multiplicative-large-monoid-Large-Ring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    distributive-power-add-Large-Ring :
      {l : Level} (m n : ℕ) {x : type-Large-Ring R l} →
      power-Large-Ring R (m +ℕ n) x ＝
      mul-Large-Ring R (power-Large-Ring R m x) (power-Large-Ring R n x)
    distributive-power-add-Large-Ring =
      distributive-power-add-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    power-mul-Large-Ring :
      {l : Level} (m n : ℕ) {x : type-Large-Ring R l} →
      power-Large-Ring R (m *ℕ n) x ＝
      power-Large-Ring R n (power-Large-Ring R m x)
    power-mul-Large-Ring =
      power-mul-Large-Monoid
        ( multiplicative-large-monoid-Large-Ring R)
```
