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
open import foundation.inhabited-types
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.propositions

open import logic.propositionally-decidable-types

open import set-theory.cardinality-projective-sets
open import set-theory.cardinality-recursive-sets
open import set-theory.cardinals
open import set-theory.inhabited-cardinals
```

</details>

## Idea

Given a family of cardinals $κ : I → \mathrm{Cardinal}$ over a
[cardinality-recursive set](set-theory.cardinality-recursive-sets.md) $I$, then
we may define the {{#concept "dependent product cardinal" Agda=Π-Cardinal'}}
$Π_{i∈I}κᵢ$, as the cardinality of the
[dependent product](foundation.dependent-function-types.md) of any family of
representing sets $Kᵢ$.

## Definitions

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  cardinality-Π : (type-Set X → Set l2) → Cardinal (l1 ⊔ l2)
  cardinality-Π Y = cardinality (Π-Set X Y)
```

### Dependent products of cardinals over cardinality-recursive sets

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Recursive-Set l1 l2)
  (let set-X = set-Cardinality-Recursive-Set X)
  where

  Π-Cardinal' :
    (type-Set set-X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Π-Cardinal' Y =
    map-trunc-Set (Π-Set set-X) (unit-Cardinality-Recursive-Set X Y)

  compute-Π-Cardinal' :
    (K : type-Cardinality-Recursive-Set X → Set l2) →
    Π-Cardinal' (cardinality ∘ K) ＝ cardinality (Π-Set set-X K)
  compute-Π-Cardinal' K =
    equational-reasoning
      map-trunc-Set
        ( Π-Set set-X)
        ( unit-Cardinality-Recursive-Set X (cardinality ∘ K))
      ＝ map-trunc-Set (Π-Set set-X) (unit-trunc-Set K)
        by
          ap
            ( map-trunc-Set (Π-Set set-X))
            ( compute-unit-Cardinality-Recursive-Set X K)
      ＝ cardinality (Π-Set set-X K)
        by naturality-unit-trunc-Set (Π-Set set-X) K
```

### Dependent products of cardinals over cardinality-projective sets

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  where

  Π-Cardinal :
    (type-Cardinality-Projective-Set X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Π-Cardinal =
    Π-Cardinal' (cardinality-recursive-set-Cardinality-Projective-Set X)

  compute-Π-Cardinal :
    (Y : type-Cardinality-Projective-Set X → Set l2) →
    Π-Cardinal (cardinality ∘ Y) ＝
    cardinality (Π-Set (set-Cardinality-Projective-Set X) Y)
  compute-Π-Cardinal =
    compute-Π-Cardinal' (cardinality-recursive-set-Cardinality-Projective-Set X)
```

## Properties

### Dependent products of inhabited cardinals are inhabited

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  (let type-X = type-Cardinality-Projective-Set X)
  where

  is-inhabited-Π-Cardinal :
    (K : type-X → Cardinal l2) →
    ((x : type-X) → is-inhabited-Cardinal (K x)) →
    is-inhabited-Cardinal (Π-Cardinal X K)
  is-inhabited-Π-Cardinal =
    ind-Cardinality-Projective-Set X
      ( λ K →
        set-Prop
          ( function-Prop
            ( (x : type-X) → is-inhabited-Cardinal (K x))
            ( is-inhabited-prop-Cardinal (Π-Cardinal X K))))
      ( λ Y y →
        inv-tr
          ( is-inhabited-Cardinal)
          ( compute-Π-Cardinal X Y)
          ( unit-is-inhabited-cardinality
            ( Π-Set (set-Cardinality-Projective-Set X) Y)
            ( is-projective-Cardinality-Projective-Set X
              ( type-Set ∘ Y)
              ( λ x → inv-unit-is-inhabited-cardinality (Y x) (y x)))))

  Π-Inhabited-Cardinal :
    (type-X → Inhabited-Cardinal l2) → Inhabited-Cardinal (l1 ⊔ l2)
  Π-Inhabited-Cardinal K =
    ( Π-Cardinal X (pr1 ∘ K) , is-inhabited-Π-Cardinal (pr1 ∘ K) (pr2 ∘ K))
```
