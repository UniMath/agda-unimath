# Cardinality-projective sets

```agda
module set-theory.cardinality-projective-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.sections
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncation-levels
open import foundation.universe-levels

open import set-theory.cardinalities
```

</details>

## Idea

For every type $X$ there is a map $║ X → Set ║₀ → (X → Cardinal)$. We call sets
$X$ for which this map has a section
{{#concept "cardinality-projective" Disamibguation="sets"}}. Over such types we
may form [dependent sum](set-theory.dependent-sums-cardinalities.md) and
[dependent product](set-theory.dependent-products-cardinalities.md) cardinals.

Note that classically, the universe of sets is itself a set, and so trivially
$║ X → Set ║₀ → (X → ║ Set ║₀)$ is an equivalence. However, with univalence,
meaning that $║ Set ║₀$ is itself the type of cardinalities, this is no longer
the case.

**Terminology.** This is nonstandard terminology and is subject to change.

## Definition

```agda
is-cardinality-projective-set-Level :
  {l1 : Level} (l2 : Level) (X : Set l1) → UU (l1 ⊔ lsuc l2)
is-cardinality-projective-set-Level l2 X =
  section (map-distributive-trunc-function-type zero-𝕋 (type-Set X) (Set l2))
```

### The universe of cardinality-projective sets at a universe level

```agda
Cardinality-Projective-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cardinality-Projective-Set l1 l2 =
  Σ (Set l1) (is-cardinality-projective-set-Level l2)

module _
  {l1 l2 : Level} (X : Cardinality-Projective-Set l1 l2)
  where

  set-Cardinality-Projective-Set : Set l1
  set-Cardinality-Projective-Set = pr1 X

  type-Cardinality-Projective-Set : UU l1
  type-Cardinality-Projective-Set = type-Set set-Cardinality-Projective-Set

  is-set-type-Cardinality-Projective-Set :
    is-set type-Cardinality-Projective-Set
  is-set-type-Cardinality-Projective-Set =
    is-set-type-Set set-Cardinality-Projective-Set

  is-cardinality-projective-Cardinality-Projective-Set :
    is-cardinality-projective-set-Level l2 set-Cardinality-Projective-Set
  is-cardinality-projective-Cardinality-Projective-Set = pr2 X

  map-section-Cardinality-Projective-Set :
    ( type-Cardinality-Projective-Set → Cardinal l2) →
    ║ (type-Cardinality-Projective-Set → Set l2) ║₀
  map-section-Cardinality-Projective-Set =
    map-section
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Projective-Set)
        ( Set l2))
      ( is-cardinality-projective-Cardinality-Projective-Set)

  is-section-map-section-Cardinality-Projective-Set :
    is-section
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Projective-Set)
        ( Set l2))
      ( map-section-Cardinality-Projective-Set)
  is-section-map-section-Cardinality-Projective-Set =
    is-section-map-section
      ( map-distributive-trunc-function-type zero-𝕋
        ( type-Cardinality-Projective-Set)
        ( Set l2))
      ( is-cardinality-projective-Cardinality-Projective-Set)
```

```text
  (X → Set)      ↖
     |      \     \
     |        \    \
     ∨          ∨   \
  (X → Card) -> ║ X → Set ║₀

              - ∘ η
  (X → Set)
     |      \
   η |        \   - ∘ η
     ∨          ↘
  ║X → Set║₀ ---> (X → Card)
             <---
              𝓈
```

Naturality says

```text
             ev x
  (X → Set) -----> Set
    |               |
  η |               | η
    ∨       ║ev x║₀ ∨
  ║X → Set║₀ ----> Card
```

```agda
  compute-map-section-at-cardinality-Cardinality-Projective-Set :
    (K : type-Cardinality-Projective-Set → Set l2) →
    map-section-Cardinality-Projective-Set (cardinality ∘ K) ＝ unit-trunc-Set K
  compute-map-section-at-cardinality-Cardinality-Projective-Set = TODO
    where postulate TODO : _
```

## See also

- In
  [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
  it is demonstrated that finite types are cardinality-projective.
