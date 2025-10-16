# Coproducts of cardinalities

```agda
module set-theory.addition-cardinalities where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.double-negation
open import foundation.equality-coproduct-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.propositions

open import logic.propositionally-decidable-types

open import set-theory.cardinalities
open import set-theory.cardinality-projective-sets
open import set-theory.equality-cardinalities
open import set-theory.inequality-cardinalities
open import set-theory.zero-cardinal
```

</details>

## Idea

Given two [cardinals](set-theory.cardinalities.lagda.md) `A` and `B`, we may
form their {{#concept "sum" Disambiguation="cardinal"  Agda=add-Cardinal}}, or
**coproduct** cardinal, `A + B`. It is defined on isomorphism classes as
[coproducts](foundation-core.coproduct-types.md) of
[sets](foundation-core.sets.md).

## Definitions

### The underlying addition of cardinalities

```agda
module _
  {l1 l2 : Level}
  where

  add-cardinality' : Set l1 → Set l2 → Cardinal (l1 ⊔ l2)
  add-cardinality' X Y = cardinality (coproduct-Set X Y)
```

### Addition of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  add-Cardinal : Cardinal l1 → Cardinal l2 → Cardinal (l1 ⊔ l2)
  add-Cardinal = binary-map-trunc-Set coproduct-Set
```

### Addition of cardinalities

```agda
module _
  {l1 l2 : Level}
  where

  add-cardinality : Set l1 → Set l2 → Cardinal (l1 ⊔ l2)
  add-cardinality X Y = add-Cardinal (cardinality X) (cardinality Y)

  compute-add-cardinality :
    (X : Set l1) (Y : Set l2) →
    add-Cardinal (cardinality X) (cardinality Y) ＝ add-cardinality' X Y
  compute-add-cardinality = {!   !}
```

## Properties

### The zero cardinal is the additive unit

```agda
module _
  {l : Level}
  where

  left-unit-law-add-Cardinal :
    {l : Level} (X : Cardinal l) → sim-Cardinal (add-Cardinal zero-Cardinal X) X
  left-unit-law-add-Cardinal X = {!   !}
```
