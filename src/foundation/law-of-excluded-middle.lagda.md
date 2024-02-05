# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.negation

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

The {{#concept "law of excluded middle" Agda=LEM}} asserts that any
[proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
module _
  (l : Level)
  where

  LEM-Prop : Prop (lsuc l)
  LEM-Prop = Π-Prop (Prop l) is-decidable-Prop

  LEM : UU (lsuc l)
  LEM = type-Prop LEM-Prop
```

## Properties

### TODO

```agda
lower-LEM : {l1 : Level} (l2 : Level) → LEM (l1 ⊔ l2) → LEM l1
lower-LEM l2 lem P =
  is-decidable-equiv (compute-raise l2 (type-Prop P)) (lem (raise-Prop l2 P))
```

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Prop :
  {l : Level} → LEM l → Prop l → Decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```
