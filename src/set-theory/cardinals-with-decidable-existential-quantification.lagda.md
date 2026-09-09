# Cardinals with decidable existential quantification

```agda
module set-theory.cardinals-with-decidable-existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.types-with-decidable-existential-quantification
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `κ`
{{#concept "has decidable existential quantification" Disambiguation="cardinal" Agda=has-decidable-∃-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class
[has decidable existential quantification](foundation.types-with-decidable-existential-quantification.md).

## Definitions

### The predicate on cardinals of having decidable existential quantification

```agda
module _
  {l : Level} (κ : Cardinal l)
  where

  has-decidable-∃-prop-Cardinal : Prop l
  has-decidable-∃-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set l)
      ( has-decidable-∃-bool-Prop ∘ type-Set)

  has-decidable-∃-Cardinal : UU l
  has-decidable-∃-Cardinal = type-Prop has-decidable-∃-prop-Cardinal

  is-prop-has-decidable-∃-Cardinal : is-prop has-decidable-∃-Cardinal
  is-prop-has-decidable-∃-Cardinal =
    is-prop-type-Prop has-decidable-∃-prop-Cardinal
```

### Cardinalities with decidable existential quantification

```agda
module _
  {l : Level} (X : Set l)
  where

  has-decidable-∃-prop-cardinality : Prop l
  has-decidable-∃-prop-cardinality =
    has-decidable-∃-prop-Cardinal (cardinality X)

  has-decidable-∃-cardinality : UU l
  has-decidable-∃-cardinality = has-decidable-∃-Cardinal (cardinality X)

  is-prop-has-decidable-∃-cardinality : is-prop has-decidable-∃-cardinality
  is-prop-has-decidable-∃-cardinality =
    is-prop-has-decidable-∃-Cardinal (cardinality X)

  eq-compute-has-decidable-∃-prop-cardinality :
    has-decidable-∃-prop-cardinality ＝ has-decidable-∃-bool-Prop (type-Set X)
  eq-compute-has-decidable-∃-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set l)
      ( has-decidable-∃-bool-Prop ∘ type-Set)
      ( X)

  eq-compute-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality ＝ has-decidable-∃-bool (type-Set X)
  eq-compute-has-decidable-∃-cardinality =
    ap type-Prop eq-compute-has-decidable-∃-prop-cardinality

  compute-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality ≃ has-decidable-∃-bool (type-Set X)
  compute-has-decidable-∃-cardinality =
    equiv-eq eq-compute-has-decidable-∃-cardinality
```

### Representatives have decidable existential quantification at every level

```agda
module _
  {l : Level} (X : Set l)
  where

  has-decidable-∃-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality X → has-decidable-∃ (type-Set X)
  has-decidable-∃-has-decidable-∃-cardinality h =
    has-decidable-∃-has-decidable-∃-bool
      ( map-equiv (compute-has-decidable-∃-cardinality X) h)
```

### The universe of cardinals with decidable existential quantification

```agda
Cardinal-With-Decidable-∃ : (l : Level) → UU (lsuc l)
Cardinal-With-Decidable-∃ l = Σ (Cardinal l) has-decidable-∃-Cardinal

is-set-Cardinal-With-Decidable-∃ :
  {l : Level} → is-set (Cardinal-With-Decidable-∃ l)
is-set-Cardinal-With-Decidable-∃ =
  is-set-type-subtype has-decidable-∃-prop-Cardinal is-set-Cardinal

Cardinal-With-Decidable-∃-Set : (l : Level) → Set (lsuc l)
Cardinal-With-Decidable-∃-Set l =
  (Cardinal-With-Decidable-∃ l , is-set-Cardinal-With-Decidable-∃)

module _
  {l : Level} (κ : Cardinal-With-Decidable-∃ l)
  where

  cardinal-Cardinal-With-Decidable-∃ : Cardinal l
  cardinal-Cardinal-With-Decidable-∃ = pr1 κ

  has-decidable-∃-cardinal-Cardinal-With-Decidable-∃ :
    has-decidable-∃-Cardinal cardinal-Cardinal-With-Decidable-∃
  has-decidable-∃-cardinal-Cardinal-With-Decidable-∃ = pr2 κ
```
