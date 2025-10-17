# The directed interval type

```agda
module simplicial-type-theory.directed-interval-type where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.noncontractible-types
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "directed interval type" Disambiguation="simplicial type theory" Agda=𝟚}}
`𝟚` is the representing type for the simplicial structure on types. It is a type
consisting of a distinct source and target element, `0₂` and `1₂`, and comes
[equipped](foundation.structure.md) with a directed relation which defines a
[total order](order-theory.total-orders.md) with `0₂` as a
[bottom element](order-theory.bottom-elements-posets.md), and `1₂` as a
[top element](order-theory.top-elements-posets.md).

In this file, we postulate the existence of the directed interval type together
with its distinct source and target elements. In the module
[`directed-relation-on-directed-interval-type`](simplicial-type-theory.directed-relation-on-directed-interval-type.md),
we postulate the existence of the directed relation on the directed interval
type.

## Postulates

### The directed interval type

```agda
postulate
  𝟚 : UU lzero

  0₂ 1₂ : 𝟚

  is-nontrivial-𝟚 : 0₂ ≠ 1₂
```

## Properties

### The directed interval type is not a proposition

```agda
is-not-prop-𝟚 : ¬ (is-prop 𝟚)
is-not-prop-𝟚 H = is-nontrivial-𝟚 (eq-is-prop H)
```

### The directed interval type is not contractible

```agda
is-not-contractible-𝟚 : is-not-contractible 𝟚
is-not-contractible-𝟚 H = is-nontrivial-𝟚 (eq-is-contr H)
```

### The directed interval type is noncontractible

```agda
is-noncontractible-𝟚' : is-noncontractible' 𝟚 1
is-noncontractible-𝟚' = (0₂ , 1₂ , is-nontrivial-𝟚)

is-noncontractible-𝟚 : is-noncontractible 𝟚
is-noncontractible-𝟚 = (1 , is-noncontractible-𝟚')
```
