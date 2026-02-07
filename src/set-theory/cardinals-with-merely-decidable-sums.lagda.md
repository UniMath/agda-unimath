# Cardinals with merely decidable sums

```agda
module set-theory.cardinals-with-merely-decidable-sums where
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
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `κ`
{{#concept "merely has decidable sums" Disambiguation="set-cardinal" Agda=merely-decidable-Σ-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class merely
[has decidable dependent pair types](foundation.types-with-decidable-dependent-pair-types.md).

## Definitions

### The predicate on cardinals of merely having decidable sums

```agda
module _
  {l1 : Level} (l2 : Level) (κ : Cardinal l1)
  where

  merely-decidable-Σ-prop-Cardinal : Prop (l1 ⊔ lsuc l2)
  merely-decidable-Σ-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( trunc-Prop ∘ has-decidable-Σ-Level l2 ∘ type-Set)

  merely-decidable-Σ-Cardinal : UU (l1 ⊔ lsuc l2)
  merely-decidable-Σ-Cardinal =
    type-Prop merely-decidable-Σ-prop-Cardinal

  is-prop-merely-decidable-Σ-Cardinal :
    is-prop merely-decidable-Σ-Cardinal
  is-prop-merely-decidable-Σ-Cardinal =
    is-prop-type-Prop merely-decidable-Σ-prop-Cardinal
```

### Cardinalities with merely decidable sums

```agda
module _
  {l1 : Level} (l2 : Level) (X : Set l1)
  where

  merely-decidable-Σ-prop-cardinality : Prop (l1 ⊔ lsuc l2)
  merely-decidable-Σ-prop-cardinality =
    merely-decidable-Σ-prop-Cardinal l2 (cardinality X)

  merely-decidable-Σ-cardinality : UU (l1 ⊔ lsuc l2)
  merely-decidable-Σ-cardinality =
    merely-decidable-Σ-Cardinal l2 (cardinality X)

module _
  {l1 l2 : Level} (X : Set l1)
  where

  is-prop-merely-decidable-Σ-cardinality :
    is-prop (merely-decidable-Σ-cardinality l2 X)
  is-prop-merely-decidable-Σ-cardinality =
    is-prop-merely-decidable-Σ-Cardinal l2 (cardinality X)

  eq-compute-merely-decidable-Σ-prop-cardinality :
    merely-decidable-Σ-prop-cardinality l2 X ＝
    trunc-Prop (has-decidable-Σ-Level l2 (type-Set X))
  eq-compute-merely-decidable-Σ-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( trunc-Prop ∘ has-decidable-Σ-Level l2 ∘ type-Set)
      ( X)

  eq-compute-merely-decidable-Σ-cardinality :
    merely-decidable-Σ-cardinality l2 X ＝
    is-inhabited (has-decidable-Σ-Level l2 (type-Set X))
  eq-compute-merely-decidable-Σ-cardinality =
    ap type-Prop eq-compute-merely-decidable-Σ-prop-cardinality

  compute-merely-decidable-Σ-cardinality :
    merely-decidable-Σ-cardinality l2 X ≃
    is-inhabited (has-decidable-Σ-Level l2 (type-Set X))
  compute-merely-decidable-Σ-cardinality =
    equiv-eq eq-compute-merely-decidable-Σ-cardinality

  unit-merely-decidable-Σ-cardinality :
    is-inhabited (has-decidable-Σ-Level l2 (type-Set X)) →
    merely-decidable-Σ-cardinality l2 X
  unit-merely-decidable-Σ-cardinality =
    map-inv-equiv compute-merely-decidable-Σ-cardinality

  inv-unit-merely-decidable-Σ-cardinality :
    merely-decidable-Σ-cardinality l2 X →
    is-inhabited (has-decidable-Σ-Level l2 (type-Set X))
  inv-unit-merely-decidable-Σ-cardinality =
    map-equiv compute-merely-decidable-Σ-cardinality
```

### The universe of cardinals with merely decidable sums

```agda
Projective-Cardinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal l1 l2 = Σ (Cardinal l1) (merely-decidable-Σ-Cardinal l2)

is-set-Projective-Cardinal :
  {l1 l2 : Level} → is-set (Projective-Cardinal l1 l2)
is-set-Projective-Cardinal {l1} {l2} =
  is-set-type-subtype (merely-decidable-Σ-prop-Cardinal l2) is-set-Cardinal

Projective-Cardinal-Set : (l1 l2 : Level) → Set (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal-Set l1 l2 =
  (Projective-Cardinal l1 l2 , is-set-Projective-Cardinal)

module _
  {l1 l2 : Level} (κ : Projective-Cardinal l1 l2)
  where

  cardinal-Projective-Cardinal : Cardinal l1
  cardinal-Projective-Cardinal = pr1 κ

  is-projective-Projective-Cardinal :
    merely-decidable-Σ-Cardinal l2 cardinal-Projective-Cardinal
  is-projective-Projective-Cardinal = pr2 κ
```
