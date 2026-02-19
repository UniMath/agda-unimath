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
open import foundation.projective-types
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
{{#concept "has decidable existential quantification" Disambiguation="set-cardinal" Agda=has-decidable-∃-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class
[has decidable existential quantification](foundation.types-with-decidable-existential-quantification.md).

## Definitions

### The predicate on cardinals of having decidable existential quantification

```agda
module _
  {l1 : Level} (l2 : Level) (κ : Cardinal l1)
  where

  has-decidable-∃-prop-Cardinal : Prop (l1 ⊔ lsuc l2)
  has-decidable-∃-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( has-decidable-∃-level-Prop l2 ∘ type-Set)

  has-decidable-∃-Cardinal : UU (l1 ⊔ lsuc l2)
  has-decidable-∃-Cardinal =
    type-Prop has-decidable-∃-prop-Cardinal

  is-prop-has-decidable-∃-Cardinal :
    is-prop has-decidable-∃-Cardinal
  is-prop-has-decidable-∃-Cardinal =
    is-prop-type-Prop has-decidable-∃-prop-Cardinal
```

### Cardinalities with decidable existential quantification

```agda
module _
  {l1 : Level} (l2 : Level) (X : Set l1)
  where

  has-decidable-∃-prop-cardinality : Prop (l1 ⊔ lsuc l2)
  has-decidable-∃-prop-cardinality =
    has-decidable-∃-prop-Cardinal l2 (cardinality X)

  has-decidable-∃-cardinality : UU (l1 ⊔ lsuc l2)
  has-decidable-∃-cardinality =
    has-decidable-∃-Cardinal l2 (cardinality X)

module _
  {l1 l2 : Level} (X : Set l1)
  where

  is-prop-has-decidable-∃-cardinality :
    is-prop (has-decidable-∃-cardinality l2 X)
  is-prop-has-decidable-∃-cardinality =
    is-prop-has-decidable-∃-Cardinal l2 (cardinality X)

  eq-compute-has-decidable-∃-prop-cardinality :
    has-decidable-∃-prop-cardinality l2 X ＝
    has-decidable-∃-level-Prop l2 (type-Set X)
  eq-compute-has-decidable-∃-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( has-decidable-∃-level-Prop l2 ∘ type-Set)
      ( X)

  eq-compute-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality l2 X ＝
    has-decidable-∃-Level l2 (type-Set X)
  eq-compute-has-decidable-∃-cardinality =
    ap type-Prop eq-compute-has-decidable-∃-prop-cardinality

  compute-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality l2 X ≃
    has-decidable-∃-Level l2 (type-Set X)
  compute-has-decidable-∃-cardinality =
    equiv-eq eq-compute-has-decidable-∃-cardinality

  unit-has-decidable-∃-cardinality :
    is-inhabited (has-decidable-∃-Level l2 (type-Set X)) →
    has-decidable-∃-cardinality l2 X
  unit-has-decidable-∃-cardinality =
    rec-trunc-Prop
      ( has-decidable-∃-prop-cardinality l2 X)
      ( map-inv-equiv compute-has-decidable-∃-cardinality)

  inv-unit-has-decidable-∃-cardinality :
    has-decidable-∃-cardinality l2 X →
    is-inhabited (has-decidable-∃-Level l2 (type-Set X))
  inv-unit-has-decidable-∃-cardinality =
    unit-trunc-Prop ∘ map-equiv compute-has-decidable-∃-cardinality
```

### The universe of cardinals with decidable existential quantification

```agda
Cardinal-With-Decidable-∃ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cardinal-With-Decidable-∃ l1 l2 = Σ (Cardinal l1) (has-decidable-∃-Cardinal l2)

is-set-Cardinal-With-Decidable-∃ :
  {l1 l2 : Level} → is-set (Cardinal-With-Decidable-∃ l1 l2)
is-set-Cardinal-With-Decidable-∃ {l1} {l2} =
  is-set-type-subtype (has-decidable-∃-prop-Cardinal l2) is-set-Cardinal

Cardinal-With-Decidable-∃-Set : (l1 l2 : Level) → Set (lsuc l1 ⊔ lsuc l2)
Cardinal-With-Decidable-∃-Set l1 l2 =
  (Cardinal-With-Decidable-∃ l1 l2 , is-set-Cardinal-With-Decidable-∃)

module _
  {l1 l2 : Level} (κ : Cardinal-With-Decidable-∃ l1 l2)
  where

  cardinal-Cardinal-With-Decidable-∃ : Cardinal l1
  cardinal-Cardinal-With-Decidable-∃ = pr1 κ

  has-decidable-∃-cardinal-Cardinal-With-Decidable-∃ :
    has-decidable-∃-Cardinal l2 cardinal-Cardinal-With-Decidable-∃
  has-decidable-∃-cardinal-Cardinal-With-Decidable-∃ = pr2 κ
```
