# The law of excluded middle

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.law-of-excluded-middle
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.universe-levels

open import foundation-core.decidable-propositions funext univalence truncations
open import foundation-core.negation
open import foundation-core.propositions

open import univalent-combinatorics.2-element-types funext univalence truncations
```

</details>

## Idea

The
{{#concept "law of excluded middle" WD="principle of excluded middle" WDID=Q468422 Agda=LEM}}
asserts that any [proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
LEM : (l : Level) → UU (lsuc l)
LEM l = (P : Prop l) → is-decidable (type-Prop P)

prop-LEM : (l : Level) → Prop (lsuc l)
prop-LEM l = Π-Prop (Prop l) (is-decidable-Prop)
```

## Properties

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
