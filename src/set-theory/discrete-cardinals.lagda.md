# Discrete cardinals

```agda
module set-theory.discrete-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `κ` is
{{#concept "discrete" Disambiguation="set-cardinal" Agda=is-discrete-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class is
[discrete](foundation.discrete-types.md), i.e., has decidable equality.

## Definitions

### The predicate on cardinals of being discrete

```agda
module _
  {l : Level} (κ : Cardinal l)
  where

  is-discrete-prop-Cardinal : Prop l
  is-discrete-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set l)
      ( has-decidable-equality-Prop ∘ type-Set)

  is-discrete-Cardinal : UU l
  is-discrete-Cardinal = type-Prop is-discrete-prop-Cardinal

  is-prop-is-discrete-Cardinal : is-prop is-discrete-Cardinal
  is-prop-is-discrete-Cardinal =
    is-prop-type-Prop is-discrete-prop-Cardinal
```

### Discrete cardinalities

```agda
module _
  {l : Level} (X : Set l)
  where

  is-discrete-prop-cardinality : Prop l
  is-discrete-prop-cardinality = is-discrete-prop-Cardinal (cardinality X)

  is-discrete-cardinality : UU l
  is-discrete-cardinality = is-discrete-Cardinal (cardinality X)

  is-prop-is-discrete-cardinality : is-prop is-discrete-cardinality
  is-prop-is-discrete-cardinality =
    is-prop-is-discrete-Cardinal (cardinality X)

  eq-compute-is-discrete-prop-cardinality :
    is-discrete-prop-cardinality ＝ has-decidable-equality-Prop (type-Set X)
  eq-compute-is-discrete-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set l)
      ( has-decidable-equality-Prop ∘ type-Set)
      ( X)

  eq-compute-is-discrete-cardinality :
    is-discrete-cardinality ＝ has-decidable-equality (type-Set X)
  eq-compute-is-discrete-cardinality =
    ap type-Prop eq-compute-is-discrete-prop-cardinality

  compute-is-discrete-cardinality :
    is-discrete-cardinality ≃ has-decidable-equality (type-Set X)
  compute-is-discrete-cardinality =
    equiv-eq eq-compute-is-discrete-cardinality

  unit-is-discrete-cardinality :
    has-decidable-equality (type-Set X) → is-discrete-cardinality
  unit-is-discrete-cardinality =
    map-inv-equiv compute-is-discrete-cardinality

  inv-unit-is-discrete-cardinality :
    is-discrete-cardinality → has-decidable-equality (type-Set X)
  inv-unit-is-discrete-cardinality =
    map-equiv compute-is-discrete-cardinality
```

### The universe of discrete cardinals

```agda
Discrete-Cardinal : (l : Level) → UU (lsuc l)
Discrete-Cardinal l = Σ (Cardinal l) is-discrete-Cardinal

is-set-Discrete-Cardinal : {l : Level} → is-set (Discrete-Cardinal l)
is-set-Discrete-Cardinal =
  is-set-type-subtype is-discrete-prop-Cardinal is-set-Cardinal

Discrete-Cardinal-Set : (l : Level) → Set (lsuc l)
Discrete-Cardinal-Set l = (Discrete-Cardinal l , is-set-Discrete-Cardinal)

module _
  {l : Level} (κ : Discrete-Cardinal l)
  where

  cardinal-Discrete-Cardinal : Cardinal l
  cardinal-Discrete-Cardinal = pr1 κ

  is-discrete-Discrete-Cardinal :
    is-discrete-Cardinal cardinal-Discrete-Cardinal
  is-discrete-Discrete-Cardinal = pr2 κ
```
