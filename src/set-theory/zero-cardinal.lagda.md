# The zero cardinal

```agda
module set-theory.zero-cardinal where
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

open import set-theory.cardinality-projective-sets
open import set-theory.cardinals
open import set-theory.inequality-cardinals
```

</details>

## Idea

The {{#concept "zero cardinal" Agda=zero-Cardinal}}, or **empty cardinal**, is
the isomorphism class of [empty](foundation.empty-types.md)
[sets](foundation-core.sets.md).

## Definitions

```agda
zero-Cardinal : Cardinal lzero
zero-Cardinal = cardinality empty-Set
```

## Properties

### Any cardinal less than or equal to the zero cardinal is the zero cardinal

> This remains to be formalized.
