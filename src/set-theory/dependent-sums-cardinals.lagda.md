# Dependent sums of cardinals

```agda
module set-theory.dependent-sums-cardinals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.double-negation
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.isolated-elements
open import foundation.logical-equivalences
open import foundation.mere-embeddings
open import foundation.negated-equality
open import foundation.negation
open import foundation.powersets
open import foundation.projective-types
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
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
```

</details>

## Idea

Given a family of cardinals $κ : I → \mathrm{Cardinal}$ over a
[cardinality-recursive set](set-theory.cardinality-recursive-sets.md) $I$, then
we may define the {{#concept "dependent sum cardinal" Agda=Σ-Cardinal'}}
$Σ_{i∈I}κᵢ$, as the cardinality of the
[dependent sum](foundation.dependent-pair-types.md) of any family of
representing sets $Kᵢ$.

## Definitions

### The cardinality of a dependent sum of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  cardinality-Σ : (type-Set X → Set l2) → Cardinal (l1 ⊔ l2)
  cardinality-Σ Y = cardinality (Σ-Set X Y)
```

### Dependent sums of cardinals over cardinality-recursive sets

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Recursive-Set l1 l2)
  (let set-X = set-Cardinality-Recursive-Set X)
  (let type-X = type-Cardinality-Recursive-Set X)
  where

  Σ-Cardinal' :
    (type-X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Σ-Cardinal' K =
    map-trunc-Set (Σ-Set set-X) (unit-Cardinality-Recursive-Set X K)

  compute-Σ-Cardinal' :
    (Y : type-X → Set l2) →
    Σ-Cardinal' (cardinality ∘ Y) ＝ cardinality (Σ-Set set-X Y)
  compute-Σ-Cardinal' Y =
    equational-reasoning
      Σ-Cardinal' (cardinality ∘ Y)
      ＝ map-trunc-Set (Σ-Set set-X) (unit-trunc-Set Y)
        by
          ap
            ( map-trunc-Set (Σ-Set set-X))
            ( compute-unit-Cardinality-Recursive-Set X Y)
      ＝ cardinality (Σ-Set set-X Y)
        by naturality-unit-trunc-Set (Σ-Set set-X) Y
```

### Dependent sums of cardinals over cardinality-projective sets

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  where

  Σ-Cardinal :
    (type-Cardinality-Projective-Set X → Cardinal l2) → Cardinal (l1 ⊔ l2)
  Σ-Cardinal =
    Σ-Cardinal' (cardinality-recursive-set-Cardinality-Projective-Set X)

  compute-Σ-Cardinal :
    (Y : type-Cardinality-Projective-Set X → Set l2) →
    Σ-Cardinal (cardinality ∘ Y) ＝
    cardinality (Σ-Set (set-Cardinality-Projective-Set X) Y)
  compute-Σ-Cardinal =
    compute-Σ-Cardinal' (cardinality-recursive-set-Cardinality-Projective-Set X)
```

## Properties

### Dependent sums of inhabited cardinals are inhabited

```agda
module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  (let type-X = type-Cardinality-Projective-Set X)
  (|x| : is-inhabited type-X)
  where

  is-inhabited-Σ-Cardinal :
    (K : type-X → Cardinal l2) →
    ((x : type-X) → is-inhabited-Cardinal (K x)) →
    is-inhabited-Cardinal (Σ-Cardinal X K)
  is-inhabited-Σ-Cardinal =
    ind-Cardinality-Projective-Set X
      ( λ K →
        set-Prop
          ( function-Prop
            ( (x : type-X) → is-inhabited-Cardinal (K x))
            ( is-inhabited-prop-Cardinal (Σ-Cardinal X K))))
      ( λ Y y →
        inv-tr
          ( is-inhabited-Cardinal)
          ( compute-Σ-Cardinal X Y)
          ( unit-is-inhabited-cardinality
            ( Σ-Set (set-Cardinality-Projective-Set X) Y)
            ( is-inhabited-Σ
              ( |x|)
              ( λ x → inv-unit-is-inhabited-cardinality (Y x) (y x)))))

  Σ-Inhabited-Cardinal :
    (type-X → Inhabited-Cardinal l2) → Inhabited-Cardinal (l1 ⊔ l2)
  Σ-Inhabited-Cardinal K =
    ( Σ-Cardinal X (pr1 ∘ K) , is-inhabited-Σ-Cardinal (pr1 ∘ K) (pr2 ∘ K))
```

### Inequality is preserved under dependent sums over projective types

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  (is-projective-X : is-projective-Level' l2 (type-Set X))
  where

  leq-cardinality-Σ :
    (K P : type-Set X → Set l2) →
    ((i : type-Set X) → leq-cardinality (K i) (P i)) →
    leq-cardinality (Σ-Set X K) (Σ-Set X P)
  leq-cardinality-Σ K P f =
    unit-leq-cardinality
      ( Σ-Set X K)
      ( Σ-Set X P)
      ( mere-emb-tot
        ( is-projective-X)
        ( λ x → inv-unit-leq-cardinality (K x) (P x) (f x)))
```

TODO

```text
module _
  {l1 l2 : Level} (X : Cardinality-Recursive-Set l1 l2)
  (let type-X = type-Cardinality-Recursive-Set X)
  (is-projective-X : is-projective-Level' l2 (type-Cardinality-Recursive-Set X))
  where

  leq-Σ-Cardinal' :
    (K P : type-X → Cardinal l2) →
    ((i : type-X) → leq-Cardinal (K i) (P i)) →
    leq-Cardinal (Σ-Cardinal' X K) (Σ-Cardinal' X P)
  leq-Σ-Cardinal' K P f = {!   !}
  -- proof somehow proceeds by using that since `X` is cardinality-recursive, it suffices to show this for families of sets, and then it's just an easy fact of dependent sums.
```
