# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

The law of excluded middle asserts that any proposition `P` is decidable.

## Definition

```agda
LEM : (l : Level) → UU (lsuc l)
LEM l = (P : Prop l) → is-decidable (type-Prop P)
```

## Properties

### Given LEM, we obtain a map from the type of propositions to the type of all propositions

```agda
decidable-prop-Prop :
  {l : Level} → LEM l → Prop l → decidable-Prop l
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
    is-not-decidable-type-UU-Fin-two-ℕ (λ X → d (pr1 X))
```
