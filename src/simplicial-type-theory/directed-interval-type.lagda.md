# The directed interval type

```agda
module simplicial-type-theory.directed-interval-type where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.mere-equality
open import foundation.negated-equality
open import foundation.negation
open import foundation.noncontractible-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
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
[`directed-relation-directed-interval-type`](simplicial-type-theory.directed-relation-directed-interval-type.md),
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

### The canonical inclusion of the booleans into the directed interval

The canonical inclusion of the booleans into the directed interval is the map
that sends `false` to `0₂` and `true` to `1₂`. Using the nontriviality of `𝟚`,
we can already show that this map is
[injective](foundation-core.injective-maps.md).

```agda
map-directed-interval-bool : bool → 𝟚
map-directed-interval-bool true = 1₂
map-directed-interval-bool false = 0₂

is-injective-map-directed-interval-bool :
  is-injective map-directed-interval-bool
is-injective-map-directed-interval-bool {true} {true} p =
  refl
is-injective-map-directed-interval-bool {true} {false} p =
  ex-falso (is-nontrivial-𝟚 (inv p))
is-injective-map-directed-interval-bool {false} {true} p =
  ex-falso (is-nontrivial-𝟚 p)
is-injective-map-directed-interval-bool {false} {false} p =
  refl

is-retraction-is-injective-map-directed-interval-bool :
  {x y : bool} →
  is-retraction
    ( ap map-directed-interval-bool {x} {y})
    ( is-injective-map-directed-interval-bool)
is-retraction-is-injective-map-directed-interval-bool {true} {true} refl =
  refl
is-retraction-is-injective-map-directed-interval-bool {false} {false} refl =
  refl

retraction-ap-map-directed-interval-bool :
  {x y : bool} → retraction (ap map-directed-interval-bool {x} {y})
retraction-ap-map-directed-interval-bool =
  ( is-injective-map-directed-interval-bool ,
    is-retraction-is-injective-map-directed-interval-bool)
```

We show that `map-directed-interval-bool` is an
[embedding](foundation-core.embeddings.md) in
[`directed-relation-directed-interval-type`](simplicial-type-theory.directed-relation-directed-interval-type.md).

### The directed interval is not connected

**Proof.** A type is 0-connected only if all pairs of elements are
[merely equal](foundation.mere-equality.md), and since we are attempting to
deduce a contradiction we may assume we have that all elements are equal, but
`0₂` and `1₂` are not.

```agda
is-not-0-connected-𝟚 : ¬ (is-0-connected 𝟚)
is-not-0-connected-𝟚 H =
  rec-trunc-Prop empty-Prop is-nontrivial-𝟚 (mere-eq-is-0-connected H 0₂ 1₂)
```
