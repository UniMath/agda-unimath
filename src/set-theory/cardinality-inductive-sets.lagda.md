# Cardinality-inductive sets

```agda
module set-theory.cardinality-inductive-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.mere-equivalences
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

For every type $X$ there is a map $║X → Set║₀ → (X → \mathrm{Cardinal})$. We
call [sets](foundation-core.sets.md) $X$ for which this map is a retract
{{#concept "cardinality-inductive" Disamibguation="sets" Agda=Cardinality-Inductive-Set}}.
Over such sets we may form
[dependent sum](set-theory.dependent-sums-cardinals.md) and
[dependent product](set-theory.dependent-products-cardinals.md)
[cardinals](set-theory.cardinals.md).

Note that classically, the universe of sets is itself a set, and so trivially
$║X → \mathrm{Set}║₀ ≃ (X → ║\mathrm{Set}║₀)$. However, with univalence, the
universe of sets $\mathrm{Set}$ brandishes higher structure, and its set
truncation $║Set║₀$ presents cardinals.

```text
            (X → Set)
           /        \
    surj  ∨          \
         ∨            ∨
  ║X → Set║₀ ╰-----> (X → Cardinality)
              <<---
```

**Terminology.** This is nonstandard terminology and may be subject to change.

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (X : Set l1)
  where

  is-cardinality-inductive-set-Level : UU (l1 ⊔ lsuc l2)
  is-cardinality-inductive-set-Level =
    retraction
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set X) (Set l2))
```

### The universe of cardinality-inductive sets at a universe level

```agda
Cardinality-Inductive-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cardinality-Inductive-Set l1 l2 =
  Σ (Set l1) (is-cardinality-inductive-set-Level l2)

module _
  {l1 l2 : Level} (X : Cardinality-Inductive-Set l1 l2)
  where

  set-Cardinality-Inductive-Set : Set l1
  set-Cardinality-Inductive-Set = pr1 X

  type-Cardinality-Inductive-Set : UU l1
  type-Cardinality-Inductive-Set = type-Set set-Cardinality-Inductive-Set

  is-set-type-Cardinality-Inductive-Set :
    is-set type-Cardinality-Inductive-Set
  is-set-type-Cardinality-Inductive-Set =
    is-set-type-Set set-Cardinality-Inductive-Set

  is-cardinality-inductive-Cardinality-Inductive-Set :
    is-cardinality-inductive-set-Level l2 set-Cardinality-Inductive-Set
  is-cardinality-inductive-Cardinality-Inductive-Set = pr2 X

  unit-Cardinality-Inductive-Set :
    ( type-Cardinality-Inductive-Set → Cardinal l2) →
    ║ (type-Cardinality-Inductive-Set → Set l2) ║₀
  unit-Cardinality-Inductive-Set =
    map-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Inductive-Set)
        ( Set l2))
      ( is-cardinality-inductive-Cardinality-Inductive-Set)

  is-retraction-unit-Cardinality-Inductive-Set :
    is-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Inductive-Set)
        ( Set l2))
      ( unit-Cardinality-Inductive-Set)
  is-retraction-unit-Cardinality-Inductive-Set =
    is-retraction-map-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Inductive-Set)
        ( Set l2))
      ( is-cardinality-inductive-Cardinality-Inductive-Set)

  retract-Cardinality-Inductive-Set :
    ║ (type-Cardinality-Inductive-Set → Set l2) ║₀ retract-of
    ( type-Cardinality-Inductive-Set → Cardinal l2)
  retract-Cardinality-Inductive-Set =
    ( ( map-distributive-trunc-function-type
        ( zero-𝕋)
        ( type-Cardinality-Inductive-Set)
        ( Set l2)) ,
      ( is-cardinality-inductive-Cardinality-Inductive-Set))

  compute-unit-Cardinality-Inductive-Set :
    (K : type-Cardinality-Inductive-Set → Set l2) →
    unit-Cardinality-Inductive-Set (cardinality ∘ K) ＝ unit-trunc-Set K
  compute-unit-Cardinality-Inductive-Set K =
    equational-reasoning
      unit-Cardinality-Inductive-Set (cardinality ∘ K)
      ＝ unit-Cardinality-Inductive-Set
          ( map-distributive-trunc-function-type zero-𝕋
            ( type-Cardinality-Inductive-Set)
            ( Set l2)
            ( unit-trunc K))
        by
          ap
            ( unit-Cardinality-Inductive-Set)
            ( inv (eq-htpy (compute-distributive-trunc-function-type zero-𝕋 K)))
      ＝ unit-trunc K
        by is-retraction-unit-Cardinality-Inductive-Set (unit-trunc K)
```

## See also

- In
  [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
  it is demonstrated that finite types are cardinality-inductive.
