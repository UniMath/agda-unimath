# Decidable cardinals

```agda
module set-theory.decidable-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
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

open import logic.propositionally-decidable-types

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `κ` is
{{#concept "decidable" Disambiguation="set-cardinal" Agda=is-decidable-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class is
[propositionally decidable](logic.propositionally-decidable-types.md).

## Definitions

### The predicate on cardinals of being decidable

```agda
module _
  {l : Level} (κ : Cardinal l)
  where

  is-decidable-prop-Cardinal : Prop l
  is-decidable-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set l)
      ( is-inhabited-or-empty-Prop ∘ type-Set)

  is-decidable-Cardinal : UU l
  is-decidable-Cardinal = type-Prop is-decidable-prop-Cardinal

  is-prop-is-decidable-Cardinal : is-prop is-decidable-Cardinal
  is-prop-is-decidable-Cardinal =
    is-prop-type-Prop is-decidable-prop-Cardinal
```

### Decidable cardinalities

```agda
module _
  {l : Level} (X : Set l)
  where

  is-decidable-prop-cardinality : Prop l
  is-decidable-prop-cardinality = is-decidable-prop-Cardinal (cardinality X)

  is-decidable-cardinality : UU l
  is-decidable-cardinality = is-decidable-Cardinal (cardinality X)

  is-prop-is-decidable-cardinality : is-prop is-decidable-cardinality
  is-prop-is-decidable-cardinality =
    is-prop-is-decidable-Cardinal (cardinality X)

  eq-compute-is-decidable-prop-cardinality :
    is-decidable-prop-cardinality ＝ is-inhabited-or-empty-Prop (type-Set X)
  eq-compute-is-decidable-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set l)
      ( is-inhabited-or-empty-Prop ∘ type-Set)
      ( X)

  eq-compute-is-decidable-cardinality :
    is-decidable-cardinality ＝ is-inhabited-or-empty (type-Set X)
  eq-compute-is-decidable-cardinality =
    ap type-Prop eq-compute-is-decidable-prop-cardinality

  compute-is-decidable-cardinality :
    is-decidable-cardinality ≃ is-inhabited-or-empty (type-Set X)
  compute-is-decidable-cardinality =
    equiv-eq eq-compute-is-decidable-cardinality

  unit-is-decidable-cardinality :
    is-inhabited-or-empty (type-Set X) → is-decidable-cardinality
  unit-is-decidable-cardinality =
    map-inv-equiv compute-is-decidable-cardinality

  inv-unit-is-decidable-cardinality :
    is-decidable-cardinality → is-inhabited-or-empty (type-Set X)
  inv-unit-is-decidable-cardinality =
    map-equiv compute-is-decidable-cardinality
```

### The universe of decidable cardinals

```agda
decidable-Cardinal : (l : Level) → UU (lsuc l)
decidable-Cardinal l = Σ (Cardinal l) is-decidable-Cardinal

is-set-decidable-Cardinal : {l : Level} → is-set (decidable-Cardinal l)
is-set-decidable-Cardinal =
  is-set-type-subtype is-decidable-prop-Cardinal is-set-Cardinal

decidable-Cardinal-Set : (l : Level) → Set (lsuc l)
decidable-Cardinal-Set l = (decidable-Cardinal l , is-set-decidable-Cardinal)

module _
  {l : Level} (κ : decidable-Cardinal l)
  where

  cardinal-decidable-Cardinal : Cardinal l
  cardinal-decidable-Cardinal = pr1 κ

  is-decidable-decidable-Cardinal :
    is-decidable-Cardinal cardinal-decidable-Cardinal
  is-decidable-decidable-Cardinal = pr2 κ
```
