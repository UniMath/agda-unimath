# Dependent products of cardinals

```agda
module set-theory.dependent-products-cardinals where
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

open import set-theory.cardinality-inductive-sets
open import set-theory.cardinals
```

</details>

## Idea

Given a family of cardinals $κ : I → \mathrm{Cardinal}$ over a
[cardinality-projective set](set-theory.cardinality-projective-sets.md) $I$,
then we may define the {{#concept "dependent product cardinal" Agda=Π-Cardinal}}
$Π_{i∈I}κᵢ$, as the cardinality of the
[dependent product](foundation.dependent-function-types.md) of any family of
representing sets $Kᵢ$.

## Definitions

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Inductive-Set l1 l2)
  where

  Π-Cardinal :
    (type-Cardinality-Inductive-Set X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Π-Cardinal Y =
    map-trunc-Set
      ( Π-Set (set-Cardinality-Inductive-Set X))
      ( unit-Cardinality-Inductive-Set X Y)

  compute-Π-Cardinal :
    (K : type-Cardinality-Inductive-Set X → Set l2) →
    Π-Cardinal (cardinality ∘ K) ＝
    cardinality (Π-Set (set-Cardinality-Inductive-Set X) K)
  compute-Π-Cardinal K =
    equational-reasoning
      map-trunc-Set
        ( Π-Set (set-Cardinality-Inductive-Set X))
        ( unit-Cardinality-Inductive-Set X (cardinality ∘ K))
      ＝ map-trunc-Set (Π-Set (pr1 X)) (unit-trunc-Set K)
        by
          ap
            ( map-trunc-Set (Π-Set (set-Cardinality-Inductive-Set X)))
            ( compute-unit-Cardinality-Inductive-Set X K)
      ＝ cardinality
          ( Π-Set (set-Cardinality-Inductive-Set X) K)
        by
          naturality-unit-trunc-Set (Π-Set (set-Cardinality-Inductive-Set X)) K
```
