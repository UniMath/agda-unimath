# Dependent sums of cardinals

```agda
module set-theory.dependent-sums-cardinals where
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

open import set-theory.cardinality-projective-sets
open import set-theory.cardinals
open import set-theory.inequality-cardinals
```

</details>

## Idea

Given a family of cardinals $κ : I → \mathrm{Cardinal}$ over a
[cardinality-projective set](set-theory.cardinality-projective-sets.md) $I$,
then we may define the {{#concept "dependent sum cardinal"}} $Σ_{i∈I}κᵢ$, as the
cardinality of the [dependent sum](foundation.dependent-pair-types.md) of any
family of representing sets $Kᵢ$.

## Definitions

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  where

  Σ-Cardinal :
    (type-Cardinality-Projective-Set X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Σ-Cardinal Y =
    map-trunc-Set
      ( Σ-Set (set-Cardinality-Projective-Set X))
      ( map-section-Cardinality-Projective-Set X Y)

  compute-Σ-Cardinal :
    (K : type-Cardinality-Projective-Set X → Set l2) →
    Σ-Cardinal (cardinality ∘ K) ＝
    cardinality (Σ-Set (set-Cardinality-Projective-Set X) K)
  compute-Σ-Cardinal K =
    equational-reasoning
      map-trunc-Set
        ( Σ-Set (set-Cardinality-Projective-Set X))
        ( map-section-Cardinality-Projective-Set X (cardinality ∘ K))
      ＝ map-trunc-Set (Σ-Set (pr1 X)) (unit-trunc-Set K)
        by
          ap
            ( map-trunc-Set (Σ-Set (set-Cardinality-Projective-Set X)))
            ( compute-map-section-at-cardinality-Cardinality-Projective-Set X K)
      ＝ cardinality
          ( Σ-Set (set-Cardinality-Projective-Set X) K)
        by
          naturality-unit-trunc-Set (Σ-Set (set-Cardinality-Projective-Set X)) K
```

## Properties

### Inequality is preserved under dependent sums

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  where

  leq-Σ-Cardinal :
    (K P : type-Cardinality-Projective-Set X → Cardinal l2) →
    ((i : type-Cardinality-Projective-Set X) → leq-Cardinal (K i) (P i)) →
    leq-Cardinal (Σ-Cardinal X K) (Σ-Cardinal X P)
  leq-Σ-Cardinal K P f = {!   !}
  -- proof somehow proceeds by using that since `X` is cardinality-projective, it suffices to show this for families of sets, and then it's just an easy fact of dependent sums.
```
