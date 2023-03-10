# Nilpotent elements in rings

```agda
module ring-theory.nilpotent-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A nilpotent element in a ring is an element `x` for which there is a natural number `n` such that `x^n = 0`.

## Definition

```agda
is-nilpotent-element-ring-Prop :
  {l : Level} (R : Ring l) → type-Ring R → Prop l
is-nilpotent-element-ring-Prop R x = ∃-Prop ℕ (λ n → Id (power-Ring R n x) (zero-Ring R))

is-nilpotent-element-Ring : {l : Level} (R : Ring l) → type-Ring R → UU l
is-nilpotent-element-Ring R x = type-Prop (is-nilpotent-element-ring-Prop R x)

is-prop-is-nilpotent-element-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  is-prop (is-nilpotent-element-Ring R x)
is-prop-is-nilpotent-element-Ring R x =
  is-prop-type-Prop (is-nilpotent-element-ring-Prop R x)
```
