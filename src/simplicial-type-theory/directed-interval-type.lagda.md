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
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.fibers-of-maps
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
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
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
[`inequality-directed-interval-type`](simplicial-type-theory.inequality-directed-interval-type.md),
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
noncontractibility-𝟚' : noncontractibility' 𝟚 1
noncontractibility-𝟚' = (0₂ , 1₂ , is-nontrivial-𝟚)

noncontractibility-𝟚 : noncontractibility 𝟚
noncontractibility-𝟚 = (1 , noncontractibility-𝟚')

is-noncontractible-𝟚 : is-noncontractible 𝟚
is-noncontractible-𝟚 = unit-trunc-Prop noncontractibility-𝟚
```

## Definitions

### The boundary of the directed interval

```agda
subtype-∂𝟚' : subtype lzero 𝟚
subtype-∂𝟚' t =
  coproduct-Prop
    ( mere-eq-Prop t 0₂)
    ( mere-eq-Prop t 1₂)
    ( λ |t=0| →
      rec-trunc-Prop empty-Prop
        ( λ t=1 →
          rec-trunc-Prop empty-Prop
            ( λ t=0 → is-nontrivial-𝟚 (inv t=0 ∙ t=1))
            ( |t=0|)))

∂𝟚 : UU lzero
∂𝟚 = type-subtype subtype-∂𝟚'
```

### The canonical inclusion of the booleans into the directed interval

The canonical inclusion of the booleans into the directed interval is the map
that sends `false` to `0₂` and `true` to `1₂`. We call the
[image](foundation.images.md) of this map the boundary of the directed interval,
`∂𝟚`, and we show that `bool` is a [retract](foundation.retracts-of-types.md) of
`∂𝟚`.

```agda
map-boundary-directed-interval-bool : bool → ∂𝟚
map-boundary-directed-interval-bool true = (1₂ , inr (refl-mere-eq 1₂))
map-boundary-directed-interval-bool false = (0₂ , inl (refl-mere-eq 0₂))

map-bool-boundary-directed-interval : ∂𝟚 → bool
map-bool-boundary-directed-interval (t , inl x) = false
map-bool-boundary-directed-interval (t , inr x) = true

is-retraction-map-bool-boundary-directed-interval :
  is-retraction
    ( map-boundary-directed-interval-bool)
    ( map-bool-boundary-directed-interval)
is-retraction-map-bool-boundary-directed-interval true = refl
is-retraction-map-bool-boundary-directed-interval false = refl

is-surjective-map-bool-boundary-directed-interval :
  is-surjective map-bool-boundary-directed-interval
is-surjective-map-bool-boundary-directed-interval =
  is-surjective-has-section
    ( map-boundary-directed-interval-bool ,
      is-retraction-map-bool-boundary-directed-interval)

is-surjective-map-boundary-directed-interval-bool :
  is-surjective map-boundary-directed-interval-bool
is-surjective-map-boundary-directed-interval-bool (t , inl |p|) =
  rec-trunc-Prop
    ( trunc-Prop (fiber map-boundary-directed-interval-bool (t , inl |p|)))
    ( λ t=0 → unit-trunc-Prop (false , eq-type-subtype subtype-∂𝟚' (inv t=0)))
    ( |p|)
is-surjective-map-boundary-directed-interval-bool (t , inr |p|) =
  rec-trunc-Prop
    ( trunc-Prop (fiber map-boundary-directed-interval-bool (t , inr |p|)))
    ( λ t=1 → unit-trunc-Prop (true , eq-type-subtype subtype-∂𝟚' (inv t=1)))
    ( |p|)

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
is-retraction-is-injective-map-directed-interval-bool {true} refl = refl
is-retraction-is-injective-map-directed-interval-bool {false} refl = refl

retraction-ap-map-directed-interval-bool :
  {x y : bool} → retraction (ap map-directed-interval-bool {x} {y})
retraction-ap-map-directed-interval-bool =
  ( is-injective-map-directed-interval-bool ,
    is-retraction-is-injective-map-directed-interval-bool)
```

We show that `map-directed-interval-bool` is an
[embedding](foundation-core.embeddings.md) in
[`inequality-directed-interval-type`](simplicial-type-theory.inequality-directed-interval-type.md).

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
