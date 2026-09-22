# Sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "sequential diagram of isometries between metric spaces" Agda=sequential-diagram-isometry-Metric-Space}}
is a [sequence](lists.sequences.md) of
[metric spaces](metric-spaces.metric-spaces.md) `M : ℕ → Metric-Space` equipped
with a sequence of isometries `fₙ : Mₙ → Mₙ₊₁` for all `n : ℕ`.

They can be represented by diagrams of isometries

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

extending infinitely to the right.

## Definitions

### Sequential diagrams of isometries

```agda
seq-isometry-sequence-Metric-Space :
  {l1 l2 : Level} → (ℕ → Metric-Space l1 l2) → UU (l1 ⊔ l2)
seq-isometry-sequence-Metric-Space M =
  (n : ℕ) → isometry-Metric-Space (M n) (M (succ-ℕ n))

sequential-diagram-isometry-Metric-Space :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
sequential-diagram-isometry-Metric-Space l1 l2 =
  Σ (ℕ → Metric-Space l1 l2) seq-isometry-sequence-Metric-Space

module _
  {l1 l2 : Level} (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  seq-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) → Metric-Space l1 l2
  seq-metric-space-sequential-diagram-isometry-Metric-Space = pr1 M

  family-sequential-diagram-isometry-Metric-Space : (n : ℕ) → UU l1
  family-sequential-diagram-isometry-Metric-Space n =
    type-Metric-Space
      (seq-metric-space-sequential-diagram-isometry-Metric-Space n)

  seq-isometry-sequential-diagram-isometry-Metric-Space :
    seq-isometry-sequence-Metric-Space
      seq-metric-space-sequential-diagram-isometry-Metric-Space
  seq-isometry-sequential-diagram-isometry-Metric-Space = pr2 M

  seq-map-isometry-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space n →
    family-sequential-diagram-isometry-Metric-Space (succ-ℕ n)
  seq-map-isometry-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space (succ-ℕ n))
      ( seq-isometry-sequential-diagram-isometry-Metric-Space n)

  diagram-sequential-diagram-isometry-Metric-Space : sequential-diagram l1
  diagram-sequential-diagram-isometry-Metric-Space =
    ( family-sequential-diagram-isometry-Metric-Space ,
      seq-map-isometry-sequential-diagram-isometry-Metric-Space)
```

### Total space of a sequential diagram

```agda
module _
  {l1 l2 : Level} (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  tot-metric-space-sequential-diagram-isometry-Metric-Space : Metric-Space l1 l2
  tot-metric-space-sequential-diagram-isometry-Metric-Space =
    indexed-sum-Metric-Space
      ( ℕ-Set)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M)

  seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( tot-metric-space-sequential-diagram-isometry-Metric-Space)
  seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space =
    isometry-emb-fiber-indexed-Metric-Space
      ( ℕ-Set)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M)

  seq-map-tot-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space M n →
    Σ ℕ (family-sequential-diagram-isometry-Metric-Space M)
  seq-map-tot-metric-space-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( tot-metric-space-sequential-diagram-isometry-Metric-Space)
      ( seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space
        ( n))
```

### Shifts of sequential diagrams of isometries

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  shift-sequential-diagram-isometry-Metric-Space :
    sequential-diagram-isometry-Metric-Space l1 l2
  pr1 shift-sequential-diagram-isometry-Metric-Space n =
    seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ n)
  pr2 shift-sequential-diagram-isometry-Metric-Space n =
    seq-isometry-sequential-diagram-isometry-Metric-Space M (succ-ℕ n)
```

### Cocones under sequential diagrams of isometries

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( X : Metric-Space l3 l4)
  ( f :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( X))
  where

  is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space :
    Prop (l1 ⊔ l3)
  is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space =
    Π-Prop
      ( ℕ)
      ( λ n →
        htpy-map-prop-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( X)
          ( f n)
          ( comp-isometry-Metric-Space
            ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
            ( seq-metric-space-sequential-diagram-isometry-Metric-Space
              ( M)
              ( succ-ℕ n))
            ( X)
            ( f (succ-ℕ n))
            ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)))

  is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space :
    UU (l1 ⊔ l3)
  is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space =
    type-Prop
      is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space

  is-prop-is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space :
    is-prop
      is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space
  is-prop-is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space =
    is-prop-type-Prop
      is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space

module _
  { l1 l2 l3 l4 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( X : Metric-Space l3 l4)
  where

  cocone-sequential-diagram-isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-sequential-diagram-isometry-Metric-Space =
    type-subtype
      ( is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space
        ( M)
        ( X))

module _
  { l1 l2 l3 l4 : Level}
  { M : sequential-diagram-isometry-Metric-Space l1 l2}
  { X : Metric-Space l3 l4}
  ( C : cocone-sequential-diagram-isometry-Metric-Space M X)
  where

  seq-isometry-cocone-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( X)
  seq-isometry-cocone-sequential-diagram-isometry-Metric-Space = pr1 C

  coh-triangle-cocone-sequential-diagram-isometry-Metric-Space :
    is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space
      ( M)
      ( X)
      ( seq-isometry-cocone-sequential-diagram-isometry-Metric-Space)
  coh-triangle-cocone-sequential-diagram-isometry-Metric-Space = pr2 C
```

## Properties

### Induced isometries by intervals of natural numbers

If `(M , f) : M₀ → M₁ → M₂ → ...` is a sequential diagram of isometries, then
for any `i j : ℕ` with `i ≤ j`, there's an isometry `Mᵢ → Mⱼ` obtained by
composition of the `fₙ`s.

```agda
module _
  {l1 l2 : Level}
  where

  isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    leq-ℕ i j →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ H =
    id-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) H =
      comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( j)
          ( H))
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) H =
    isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( H)

  map-isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    leq-ℕ i j →
    family-sequential-diagram-isometry-Metric-Space M i →
    family-sequential-diagram-isometry-Metric-Space M j
  map-isometry-leq-sequential-diagram-isometry-Metric-Space M i j H =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j H)

  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (n : ℕ) →
    (H : leq-ℕ n n) →
    map-isometry-leq-sequential-diagram-isometry-Metric-Space M n n H ~ id
  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ H = refl-htpy
  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ n) H =
    compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( n)
      ( H)

  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (n : ℕ) →
    (H : leq-ℕ n (succ-ℕ n)) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ n))
      ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n)
        ( succ-ℕ n)
        ( H))
  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ H = refl-htpy
  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ n) H =
    compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( n)
      ( H)

  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    (H : leq-ℕ i j) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ j))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j H))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ i))
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( shift-sequential-diagram-isometry-Metric-Space M)
          ( i)
          ( j)
          ( H))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M i))
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ H = refl-htpy
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) H x =
      ap
        ( seq-map-isometry-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( j)
          ( H)
          ( x))
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) H =
    coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( H)

  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2)
    (i j : ℕ) →
    (Hi : leq-ℕ zero-ℕ i) →
    (Hj : leq-ℕ zero-ℕ j) →
    (Hij : leq-ℕ i j) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space M zero-ℕ j Hj)
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j Hij)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M zero-ℕ i Hi))
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ Hi Hj Hij = refl-htpy
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) Hi Hj Hij = refl-htpy
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) Hi Hj Hij x =
    coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( M)
      ( zero-ℕ)
      ( j)
      ( Hj)
      ( x) ∙
    compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( Hi)
      ( Hj)
      ( Hij)
      ( seq-map-isometry-sequential-diagram-isometry-Metric-Space M zero-ℕ x) ∙
    ap
      ( map-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          (succ-ℕ i))
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( shift-sequential-diagram-isometry-Metric-Space M)
          ( i)
          ( j)
          ( Hij)))
      ( inv
        ( coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( i)
          ( Hi)
          ( x)))

  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space :
    ( M : sequential-diagram-isometry-Metric-Space l1 l2) →
    ( i j k : ℕ) →
    ( Hij : leq-ℕ i j) →
    ( Hjk : leq-ℕ j k) →
    ( Hik : leq-ℕ i k) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( i)
        ( k)
        ( Hik))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M j k Hjk)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j Hij))
  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ j k Hij Hjk Hik =
    compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( M)
      ( j)
      ( k)
      ( Hij)
      ( Hik)
      ( Hjk)
  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) (succ-ℕ k) Hij Hjk Hik =
    compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( k)
      ( Hij)
      ( Hjk)
      ( Hik)
```
