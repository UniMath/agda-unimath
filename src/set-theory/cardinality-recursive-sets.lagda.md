# Cardinality-recursive sets

```agda
module set-theory.cardinality-recursive-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.identity-types
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

For every type $X$ there is a map $║ X → \Set ║₀ → (X → \Cardinal)$. We call
[sets](foundation-core.sets.md) $X$ for which this map has a
[retraction](foundation-core.retractions.md)
{{#concept "cardinality-recursive" Disamibguation="sets" Agda=Cardinality-Recursive-Set}}.
Over such sets we may form
[dependent sum](set-theory.dependent-sums-cardinals.md) and
[dependent product](set-theory.dependent-products-cardinals.md)
[cardinals](set-theory.cardinals.md).

Note that classically, the universe of sets is itself a set, and so trivially
$║ X → \Set ║₀ ≃ (X → ║ \Set ║₀)$. However, with
[univalence](foundation.univalence.md), the universe of sets $\Set$ is more
richly structured, making its [set truncation](foundation.set-truncations.md)
$║ \Set ║₀$ present cardinals.

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

  is-cardinality-recursive-set-Level : UU (l1 ⊔ lsuc l2)
  is-cardinality-recursive-set-Level =
    retraction
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set X) (Set l2))
```

### The universe of cardinality-recursive sets at a universe level

```agda
Cardinality-Recursive-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cardinality-Recursive-Set l1 l2 =
  Σ (Set l1) (is-cardinality-recursive-set-Level l2)

module _
  {l1 l2 : Level} (X : Cardinality-Recursive-Set l1 l2)
  where

  set-Cardinality-Recursive-Set : Set l1
  set-Cardinality-Recursive-Set = pr1 X

  type-Cardinality-Recursive-Set : UU l1
  type-Cardinality-Recursive-Set = type-Set set-Cardinality-Recursive-Set

  is-set-type-Cardinality-Recursive-Set :
    is-set type-Cardinality-Recursive-Set
  is-set-type-Cardinality-Recursive-Set =
    is-set-type-Set set-Cardinality-Recursive-Set

  is-cardinality-recursive-Cardinality-Recursive-Set :
    is-cardinality-recursive-set-Level l2 set-Cardinality-Recursive-Set
  is-cardinality-recursive-Cardinality-Recursive-Set = pr2 X

  unit-Cardinality-Recursive-Set :
    ( type-Cardinality-Recursive-Set → Cardinal l2) →
    ║ (type-Cardinality-Recursive-Set → Set l2) ║₀
  unit-Cardinality-Recursive-Set =
    map-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Recursive-Set)
        ( Set l2))
      ( is-cardinality-recursive-Cardinality-Recursive-Set)

  is-retraction-unit-Cardinality-Recursive-Set :
    is-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Recursive-Set)
        ( Set l2))
      ( unit-Cardinality-Recursive-Set)
  is-retraction-unit-Cardinality-Recursive-Set =
    is-retraction-map-retraction
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Recursive-Set)
        ( Set l2))
      ( is-cardinality-recursive-Cardinality-Recursive-Set)

  retract-Cardinality-Recursive-Set :
    ║ (type-Cardinality-Recursive-Set → Set l2) ║₀ retract-of
    ( type-Cardinality-Recursive-Set → Cardinal l2)
  retract-Cardinality-Recursive-Set =
    ( ( map-distributive-trunc-function-type
        ( zero-𝕋)
        ( type-Cardinality-Recursive-Set)
        ( Set l2)) ,
      ( is-cardinality-recursive-Cardinality-Recursive-Set))

  compute-unit-Cardinality-Recursive-Set :
    (K : type-Cardinality-Recursive-Set → Set l2) →
    unit-Cardinality-Recursive-Set (cardinality ∘ K) ＝ unit-trunc-Set K
  compute-unit-Cardinality-Recursive-Set K =
    equational-reasoning
      unit-Cardinality-Recursive-Set (cardinality ∘ K)
      ＝ unit-Cardinality-Recursive-Set
          ( map-distributive-trunc-function-type zero-𝕋
            ( type-Cardinality-Recursive-Set)
            ( Set l2)
            ( unit-trunc K))
        by
          ap
            ( unit-Cardinality-Recursive-Set)
            ( inv (eq-htpy (compute-distributive-trunc-function-type zero-𝕋 K)))
      ＝ unit-trunc K
        by is-retraction-unit-Cardinality-Recursive-Set (unit-trunc K)
```

## See also

- In
  [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
  it is demonstrated that finite types are cardinality-recursive.
