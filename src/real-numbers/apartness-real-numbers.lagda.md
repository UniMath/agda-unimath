# Apartness of real numbers

```agda
module real-numbers.apartness-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.disjunction
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Two real numbers are apart if one is strictly less than the other.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  apart-ℝ-Prop : Prop (l1 ⊔ l2)
  apart-ℝ-Prop = le-ℝ-Prop x y ∨ le-ℝ-Prop y x

  apart-ℝ : UU (l1 ⊔ l2)
  apart-ℝ = type-Prop apart-ℝ-Prop
```

## Properties

### If LEM, inequality implies apartness

```agda
module _
  {l1 l : Level}
  (lem : LEM l)
  (x y : ℝ l)
  where

  lem-inequality-apart-ℝ : x ≠ y → apart-ℝ x y
  lem-inequality-apart-ℝ x≠y =

```
