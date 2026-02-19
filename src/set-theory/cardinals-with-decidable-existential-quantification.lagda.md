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
{{#concept "has decidable existential quantification" Disambiguation="set-cardinal" Agda=decidable-∃-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class
[has decidable existential quantification](foundation.types-with-decidable-existential-quantification.md).

## Definitions

### The predicate on cardinals of having decidable existential quantification

```agda
module _
  {l1 : Level} (l2 : Level) (κ : Cardinal l1)
  where

  decidable-∃-prop-Cardinal : Prop (l1 ⊔ lsuc l2)
  decidable-∃-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( has-decidable-∃-level-Prop l2 ∘ type-Set)

  decidable-∃-Cardinal : UU (l1 ⊔ lsuc l2)
  decidable-∃-Cardinal =
    type-Prop decidable-∃-prop-Cardinal

  is-prop-decidable-∃-Cardinal :
    is-prop decidable-∃-Cardinal
  is-prop-decidable-∃-Cardinal =
    is-prop-type-Prop decidable-∃-prop-Cardinal
```

### Cardinalities with decidable existential quantification

```agda
module _
  {l1 : Level} (l2 : Level) (X : Set l1)
  where

  decidable-∃-prop-cardinality : Prop (l1 ⊔ lsuc l2)
  decidable-∃-prop-cardinality =
    decidable-∃-prop-Cardinal l2 (cardinality X)

  decidable-∃-cardinality : UU (l1 ⊔ lsuc l2)
  decidable-∃-cardinality =
    decidable-∃-Cardinal l2 (cardinality X)

module _
  {l1 l2 : Level} (X : Set l1)
  where

  is-prop-decidable-∃-cardinality :
    is-prop (decidable-∃-cardinality l2 X)
  is-prop-decidable-∃-cardinality =
    is-prop-decidable-∃-Cardinal l2 (cardinality X)

  eq-compute-decidable-∃-prop-cardinality :
    decidable-∃-prop-cardinality l2 X ＝
    has-decidable-∃-level-Prop l2 (type-Set X)
  eq-compute-decidable-∃-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( has-decidable-∃-level-Prop l2 ∘ type-Set)
      ( X)

  eq-compute-decidable-∃-cardinality :
    decidable-∃-cardinality l2 X ＝
    has-decidable-∃-Level l2 (type-Set X)
  eq-compute-decidable-∃-cardinality =
    ap type-Prop eq-compute-decidable-∃-prop-cardinality

  compute-decidable-∃-cardinality :
    decidable-∃-cardinality l2 X ≃
    has-decidable-∃-Level l2 (type-Set X)
  compute-decidable-∃-cardinality =
    equiv-eq eq-compute-decidable-∃-cardinality

  unit-decidable-∃-cardinality :
    is-inhabited (has-decidable-∃-Level l2 (type-Set X)) →
    decidable-∃-cardinality l2 X
  unit-decidable-∃-cardinality =
    rec-trunc-Prop
      ( decidable-∃-prop-cardinality l2 X)
      ( map-inv-equiv compute-decidable-∃-cardinality)

  inv-unit-decidable-∃-cardinality :
    decidable-∃-cardinality l2 X →
    is-inhabited (has-decidable-∃-Level l2 (type-Set X))
  inv-unit-decidable-∃-cardinality =
    unit-trunc-Prop ∘ map-equiv compute-decidable-∃-cardinality
```

### The universe of cardinals with decidable existential quantification

```agda
Projective-Cardinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal l1 l2 = Σ (Cardinal l1) (decidable-∃-Cardinal l2)

is-set-Projective-Cardinal :
  {l1 l2 : Level} → is-set (Projective-Cardinal l1 l2)
is-set-Projective-Cardinal {l1} {l2} =
  is-set-type-subtype (decidable-∃-prop-Cardinal l2) is-set-Cardinal

Projective-Cardinal-Set : (l1 l2 : Level) → Set (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal-Set l1 l2 =
  (Projective-Cardinal l1 l2 , is-set-Projective-Cardinal)

module _
  {l1 l2 : Level} (κ : Projective-Cardinal l1 l2)
  where

  cardinal-Projective-Cardinal : Cardinal l1
  cardinal-Projective-Cardinal = pr1 κ

  is-projective-Projective-Cardinal :
    decidable-∃-Cardinal l2 cardinal-Projective-Cardinal
  is-projective-Projective-Cardinal = pr2 κ
```
