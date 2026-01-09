# Zero complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.zero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.zero-real-numbers
```

</details>

## Idea

A [complex number](complex-numbers.complex-numbers.md) is zero if it is
[similar](complex-numbers.similarity-complex-numbers.md) to zero. (We use this
definition because it works at a lower universe level than equality.)

## Definition

```agda
is-zero-prop-ℂ : {l : Level} → ℂ l → Prop l
is-zero-prop-ℂ z = sim-prop-ℂ z zero-ℂ

is-zero-ℂ : {l : Level} → ℂ l → UU l
is-zero-ℂ z = sim-ℂ z zero-ℂ
```

## Properties

### `z` is zero if and only if it is equal to zero raised to the appropriate universe level

```agda
abstract
  eq-raise-zero-is-zero-ℂ :
    {l : Level} {z : ℂ l} → is-zero-ℂ z → z ＝ raise-ℂ l zero-ℂ
  eq-raise-zero-is-zero-ℂ (a~0 , b~0) =
    eq-ℂ (eq-raise-zero-is-zero-ℝ a~0) (eq-raise-zero-is-zero-ℝ b~0)

  is-zero-eq-raise-zero-ℂ :
    {l : Level} {z : ℂ l} → z ＝ raise-ℂ l zero-ℂ → is-zero-ℂ z
  is-zero-eq-raise-zero-ℂ {l} refl =
    ( is-zero-raise-zero-ℝ l , is-zero-raise-zero-ℝ l)
```
