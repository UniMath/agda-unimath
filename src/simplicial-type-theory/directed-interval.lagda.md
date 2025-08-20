# The directed interval

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-interval
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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
{{#concept "directed interval type" Disambiguation="simplicial type theory" Agda=Δ¹}}
`Δ¹` is the representing type for the simplicial structure on types. It is a
type consisting of a distinct source and target element, `0▵` and `1▵`, and
comes [equipped](foundation.structure.md) with a directed relation which defines
a [total order](order-theory.total-orders.md) with `0▵` as a
[bottom element](order-theory.bottom-elements-posets.md), and `1▵` as a
[top element](order-theory.top-elements-posets.md).

In this file, we postulate the existence of the directed interval type together
with its distinct source and target elements. In the module
[`inequality-directed-interval`](simplicial-type-theory.inequality-directed-interval.md),
we postulate the existence of the directed relation on the directed interval
type.

## Postulates

### The directed interval type

```agda
opaque
  Δ¹ : UU I1
  Δ¹ = type-Nontrivial-Bounded-Total-Order I

  0▵ : Δ¹
  0▵ = bottom-Nontrivial-Bounded-Total-Order I

  1▵ : Δ¹
  1▵ = top-Nontrivial-Bounded-Total-Order I

  is-nontrivial-Δ¹ : 0▵ ≠ 1▵
  is-nontrivial-Δ¹ = is-nontrivial-Nontrivial-Bounded-Total-Order I
```

## Properties

### The directed interval type is not a proposition

```agda
is-not-prop-Δ¹ : ¬ (is-prop Δ¹)
is-not-prop-Δ¹ H = is-nontrivial-Δ¹ (eq-is-prop H)
```

### The directed interval type is not contractible

```agda
is-not-contractible-Δ¹ : is-not-contractible Δ¹
is-not-contractible-Δ¹ H = is-nontrivial-Δ¹ (eq-is-contr H)
```

### The directed interval type is noncontractible

```agda
noncontractibility-Δ¹' : noncontractibility' Δ¹ 1
noncontractibility-Δ¹' = (0▵ , 1▵ , is-nontrivial-Δ¹)

noncontractibility-Δ¹ : noncontractibility Δ¹
noncontractibility-Δ¹ = (1 , noncontractibility-Δ¹')

is-noncontractible-Δ¹ : is-noncontractible Δ¹
is-noncontractible-Δ¹ = unit-trunc-Prop noncontractibility-Δ¹
```

## Definitions

### The boundary of the directed interval

```agda
subtype-∂Δ¹' : subtype I1 Δ¹
subtype-∂Δ¹' t =
  coproduct-Prop
    ( mere-eq-Prop t 0▵)
    ( mere-eq-Prop t 1▵)
    ( λ |t=0| →
      rec-trunc-Prop empty-Prop
        ( λ t=1 →
          rec-trunc-Prop empty-Prop
            ( λ t=0 → is-nontrivial-Δ¹ (inv t=0 ∙ t=1))
            ( |t=0|)))

∂Δ¹ : UU I1
∂Δ¹ = type-subtype subtype-∂Δ¹'
```

### The canonical inclusion of the booleans into the directed interval

The canonical inclusion of the booleans into the directed interval is the map
that sends `false` to `0▵` and `true` to `1▵`. We call the
[image](foundation.images.md) of this map the boundary of the directed interval,
`∂Δ¹`, and we show that `bool` is a [retract](foundation.retracts-of-types.md)
of `∂Δ¹`.

```agda
map-boundary-directed-interval-bool : bool → ∂Δ¹
map-boundary-directed-interval-bool true = (1▵ , inr (refl-mere-eq 1▵))
map-boundary-directed-interval-bool false = (0▵ , inl (refl-mere-eq 0▵))

map-bool-boundary-directed-interval : ∂Δ¹ → bool
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
    ( λ t=0 → unit-trunc-Prop (false , eq-type-subtype subtype-∂Δ¹' (inv t=0)))
    ( |p|)
is-surjective-map-boundary-directed-interval-bool (t , inr |p|) =
  rec-trunc-Prop
    ( trunc-Prop (fiber map-boundary-directed-interval-bool (t , inr |p|)))
    ( λ t=1 → unit-trunc-Prop (true , eq-type-subtype subtype-∂Δ¹' (inv t=1)))
    ( |p|)

map-directed-interval-bool : bool → Δ¹
map-directed-interval-bool true = 1▵
map-directed-interval-bool false = 0▵

is-injective-map-directed-interval-bool :
  is-injective map-directed-interval-bool
is-injective-map-directed-interval-bool {true} {true} p =
  refl
is-injective-map-directed-interval-bool {true} {false} p =
  ex-falso (is-nontrivial-Δ¹ (inv p))
is-injective-map-directed-interval-bool {false} {true} p =
  ex-falso (is-nontrivial-Δ¹ p)
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
[`inequality-directed-interval`](simplicial-type-theory.inequality-directed-interval.md).

### The directed interval is not connected

**Proof.** A type is 0-connected only if all pairs of elements are
[merely equal](foundation.mere-equality.md), and since we are attempting to
deduce a contradiction we may assume we have that all elements are equal, but
`0▵` and `1▵` are not equal.

```agda
is-not-0-connected-Δ¹ : ¬ (is-0-connected Δ¹)
is-not-0-connected-Δ¹ H =
  rec-trunc-Prop empty-Prop is-nontrivial-Δ¹ (mere-eq-is-0-connected H 0▵ 1▵)
```

## See also

- [`inequality-directed-interval`](simplicial-type-theory.inequality-directed-interval.md).
