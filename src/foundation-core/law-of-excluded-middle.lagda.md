# The law of excluded middle

```agda
module foundation-core.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

The
{{#concept "law of excluded middle" WD="principle of excluded middle" WDID=Q468422 Agda=LEM}}
asserts that any [proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
level-LEM : (l : Level) → UU (lsuc l)
level-LEM l = (P : Prop l) → is-decidable (type-Prop P)

LEM : UUω
LEM = {l : Level} → level-LEM l

prop-level-LEM : (l : Level) → Prop (lsuc l)
prop-level-LEM l = Π-Prop (Prop l) (is-decidable-Prop)
```

## Properties

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Prop :
  {l : Level} → level-LEM l → Prop l → Decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```
