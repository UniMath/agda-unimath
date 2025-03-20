# Bounded sums of arithmetic functions

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.bounded-sums-arithmetic-functions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functions funext
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers funext

open import foundation.coproduct-types funext
open import foundation.decidable-propositions funext
open import foundation.decidable-types funext
open import foundation.function-types funext
open import foundation.universe-levels

open import ring-theory.rings funext
```

</details>

## Idea

Given a decidable predicate `P` on the nonzero natural numbers, and a map `f`
from the nonzero natural numbers in `P` into a ring `R`, the bounded sum is a
summation of the values of `f` up to an upper bound `b`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → Decidable-Prop l') → UU (l ⊔ l')
  restricted-arithmetic-function-Ring P =
    (x : nonzero-ℕ) → type-Decidable-Prop (P x) → type-Ring R

  shift-arithmetic-function-Ring :
    type-arithmetic-functions-Ring R → type-arithmetic-functions-Ring R
  shift-arithmetic-function-Ring f = f ∘ succ-nonzero-ℕ

  shift-restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → Decidable-Prop l') →
    restricted-arithmetic-function-Ring P →
    restricted-arithmetic-function-Ring (P ∘ succ-nonzero-ℕ)
  shift-restricted-arithmetic-function-Ring P f = f ∘ succ-nonzero-ℕ

  case-one-bounded-sum-arithmetic-function-Ring :
    {l' : Level} → (P : Decidable-Prop l') →
    is-decidable (type-Decidable-Prop P) →
    (type-Decidable-Prop P → type-Ring R) → type-Ring R
  case-one-bounded-sum-arithmetic-function-Ring P (inl x) f = f x
  case-one-bounded-sum-arithmetic-function-Ring P (inr x) f =
    zero-Ring R

  bounded-sum-arithmetic-function-Ring :
    (b : ℕ) {l' : Level} (P : nonzero-ℕ → Decidable-Prop l')
    (f : restricted-arithmetic-function-Ring P) → type-Ring R
  bounded-sum-arithmetic-function-Ring zero-ℕ P f = zero-Ring R
  bounded-sum-arithmetic-function-Ring (succ-ℕ zero-ℕ) P f =
    case-one-bounded-sum-arithmetic-function-Ring
      ( P one-nonzero-ℕ)
      ( is-decidable-Decidable-Prop (P one-nonzero-ℕ))
      ( f one-nonzero-ℕ)
  bounded-sum-arithmetic-function-Ring (succ-ℕ (succ-ℕ b)) P f =
    add-Ring R
      ( case-one-bounded-sum-arithmetic-function-Ring
        ( P one-nonzero-ℕ)
        ( is-decidable-Decidable-Prop (P one-nonzero-ℕ))
        ( f one-nonzero-ℕ))
      ( bounded-sum-arithmetic-function-Ring
        ( succ-ℕ b)
        ( P ∘ succ-nonzero-ℕ)
        ( f ∘ succ-nonzero-ℕ))
```
