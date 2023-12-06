# Copartial elements

```agda
module foundation.copartial-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.universe-levels

open import foundation-core.propositions

open import orthogonal-factorization-systems.closed-modalities
```

</details>

## Idea

A {{#concept "copartial element" Agda=copartial-element}} of a type `A` is an element of type

```text
  Σ (Q : Prop), A * Q
```

where the type `P * A` is the
[join](synthetic-homotopy-theory.joins-of-types.md) of `P` and `A`. We say that
a copartial element `(P , u)` is
{{#concept "prohibited" Disambiguation="copartial element" Agda=is-prohibited-copartial-element}} if the [proposition](foundation-core.propositions.md)
`P` holds.

In order to compare copartial elements with
[partial elements](foundation.partial-elements.md), note that we have the
following [pullback squares](foundation.pullback-squares.md)

```text
  A -----> Σ (Q : Prop), A * Q        1 -----> Σ (P : Prop), (P → A)
  |                |                  |                |
  |                |                  |                |
  V                V                  V                V
  1 -----------> Prop                 1 -----------> Prop
          ⊥                                   ⊥

  1 -----> Σ (Q : Prop), A * Q        A -----> Σ (P : Prop), (P → A)
  |                |                  |                |
  |                |                  |                |
  V                V                  V                V
  1 -----------> Prop                 1 -----------> Prop
          ⊤                                   ⊤
```

Note that we make use of the
[closed modalities](orthogonal-factorization-systems.closed-modalities.md)
`A ↦ P * A` in the formulation of copartial element, whereas the formulation of
partial elements makes use of the
[open modalities](orthogonal-factorization-systems.open-modalities.md). The
concepts of partial and copartial elements are dual in that sense.

**Note:** The topic of copartial elements is not known in the literature, and
our formalization on this topic should be considered experimental.

## Definition

### Copartial elements

```agda
copartial-element : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
copartial-element l2 A =
  Σ (Prop l2) (λ Q → operator-closed-modality Q A)

module _
  {l1 l2 : Level} {A : UU l1} (a : copartial-element l2 A)
  where

  is-prohibited-prop-copartial-element : Prop l2
  is-prohibited-prop-copartial-element = pr1 a

  is-prohibited-copartial-element : UU l2
  is-prohibited-copartial-element =
    type-Prop is-prohibited-prop-copartial-element
```

### The unit of the copartial element operator

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-prohibited-prop-unit-copartial-element : Prop lzero
  is-prohibited-prop-unit-copartial-element = empty-Prop

  is-prohibited-unit-copartial-element : UU lzero
  is-prohibited-unit-copartial-element = empty

  unit-copartial-element : copartial-element lzero A
  pr1 unit-copartial-element = is-prohibited-prop-unit-copartial-element
  pr2 unit-copartial-element = unit-closed-modality empty-Prop a
```
