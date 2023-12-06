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

A {{#concept "partial element"}} of `X` consists of a
[proposition](foundation-core.propositions.md) `P` and a map `P → X`. We say
that a partial element `(P, f)` is
{{#concept "defined" Disambiguation="partial element"}} if the proposition `P`
holds.

## Definitions

### Partial elements of a type

```agda
partial-element : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
partial-element l2 X = Σ (Prop l2) (λ P → type-Prop P → X)

module _
  {l1 l2 : Level} {X : UU l1} (x : partial-element l2 X)
  where

  is-defined-prop-partial-element : Prop l2
  is-defined-prop-partial-element = pr1 x

  is-defined-partial-element : UU l2
  is-defined-partial-element = type-Prop is-defined-prop-partial-element
```

### The unit of the partial element operator

```agda
unit-partial-element :
  {l1 : Level} {X : UU l1} → X → partial-element lzero X
pr1 (unit-partial-element x) = unit-Prop
pr2 (unit-partial-element x) y = x
```

## Properties

### The type of partial elements is a directed complete poset

This remains to be shown.
[#734](https://github.com/UniMath/agda-unimath/issues/734)

## See also

- [Copartial elements](foundation.copartial-elements.md)
- [Partial function](foundation.partial-functions.md)
- [Partial sequences](elementary-number-theory.partial-sequences.md)
- [Total partial functions](foundation.total-partial-functions.md)
