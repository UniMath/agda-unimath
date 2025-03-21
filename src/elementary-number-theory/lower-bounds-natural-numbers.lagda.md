# Lower bounds of type families over the natural numbers

```agda
module elementary-number-theory.lower-bounds-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A lower bound for a type family `P` over the natural numbers is a natural number
`n` such that `P x → n ≤ x` for all `x : ℕ`.

## Definition

```agda
is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m
```

## Properties

### Being a lower bound is a property

```agda
module _
  {l1 : Level} {P : ℕ → UU l1}
  where

  abstract
    is-prop-is-lower-bound-ℕ : (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
    is-prop-is-lower-bound-ℕ x =
      is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

  is-lower-bound-ℕ-Prop : (x : ℕ) → Prop l1
  pr1 (is-lower-bound-ℕ-Prop x) = is-lower-bound-ℕ P x
  pr2 (is-lower-bound-ℕ-Prop x) = is-prop-is-lower-bound-ℕ x
```
