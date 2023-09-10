# Partial elements

```agda
module foundation.partial-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A **partial element** of `X` consists of a
[proposition](foundation-core.propositions.md) `P` and a map `P → X`. We say
that a partial element `(P, f)` is **defined** if the proposition `P` holds.

```agda
partial-element : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
partial-element l2 X = Σ (Prop l2) (λ P → type-Prop P → X)

is-defined-partial-element-Prop :
  {l1 l2 : Level} {X : UU l1} (x : partial-element l2 X) → Prop l2
is-defined-partial-element-Prop x = pr1 x

is-defined-partial-element :
  {l1 l2 : Level} {X : UU l1} (x : partial-element l2 X) → UU l2
is-defined-partial-element x = type-Prop (is-defined-partial-element-Prop x)

unit-partial-element :
  {l1 l2 : Level} {X : UU l1} → X → partial-element lzero X
pr1 (unit-partial-element x) = unit-Prop
pr2 (unit-partial-element x) y = x
```

## Properties

### The type of partial elements is a directed complete poset

This remains to be shown.
[#734](https://github.com/UniMath/agda-unimath/issues/734)
