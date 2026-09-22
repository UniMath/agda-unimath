# Limits of sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.limits-of-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.expansive-maps-pseudometric-spaces
open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.interval-isometries-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.sequential-diagrams-isometries-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

The
{{#concept "limit" Disambiguation="of a sequential diagram of isometries" Agda=metric-space-limit-sequential-diagram-isometry-Metric-Space}}
of a
[sequential diagram](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md):

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

is the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md) of
the [pseudometric space](metric-spaces.pseudometric-spaces.md) induced by the
action of the
[interval isometries](interval-isometries-sequential-diagrams-isometries-metric-spaces.md)

```text
  ϕ : (i j : ℕ) (i ≤ j) → Mᵢ → Mⱼ
```

on the total space `M∙ = Σ (n : ℕ) Mₙ`.

In other words, we consider the pseudometric structure on `M∙` such that any
`(i , xⱼ)` and `(j , xⱼ)` are `d`-neighbors in `M∙` if and only if for any
common upper bound `n` of `i` and `j`, `ϕᵢⁿ xᵢ` and `ϕⱼⁿ xⱼ` are `d`-neighbors
in `Mₙ`.

The metric quotient `M∞ = [M∙]` of `M∙` is equipped with a
[cocone](metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces.md)
under `M`:

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯ ---> M∞
```

TODO: prove the universal property of limits.

## Definitions

### The limit neighborhood on the total space of a sequential diagram

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space :
    Rational-Neighborhood-Relation
      ( l2)
      ( type-Metric-Space
        ( tot-metric-space-sequential-diagram-isometry-Metric-Space M))
  neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    d (m , xₘ) (n , xₙ) =
    Π-Prop
      ( ℕ)
      ( λ k →
        Π-Prop
          ( leq-ℕ m k)
          ( λ Hm →
            Π-Prop
              ( leq-ℕ n k)
              ( λ Hn →
                neighborhood-prop-Metric-Space
                  ( seq-metric-space-sequential-diagram-isometry-Metric-Space
                    ( M)
                    ( k))
                  ( d)
                  ( map-isometry-leq-sequential-diagram-isometry-Metric-Space
                    ( M)
                    ( m)
                    ( k)
                    ( Hm)
                    ( xₘ))
                  ( map-isometry-leq-sequential-diagram-isometry-Metric-Space
                    ( M)
                    ( n)
                    ( k)
                    ( Hn)
                    ( xₙ)))))
```

### Pseudometric limit structure

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  is-reflexive-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      ( neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space M)
  is-reflexive-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    d (n , x) k Hn Hn' =
    sim-eq-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
      ( _)
      ( _)
      ( ap
        ( λ H →
          map-isometry-leq-sequential-diagram-isometry-Metric-Space M n k H x)
        ( eq-is-prop (is-prop-leq-ℕ n k)))
      ( d)

  is-symmetric-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      ( neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space M)
  is-symmetric-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    d (m , x) (n , y) Nxy k Hm Hn =
    symmetric-neighborhood-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
      ( d)
      ( _)
      ( _)
      ( Nxy k Hn Hm)

  is-triangular-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space :
    is-triangular-Rational-Neighborhood-Relation
      ( neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space M)
  is-triangular-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    (i , xᵢ) (j , xⱼ) (k , xₖ) dij djk Njk Nij n Hi Hk =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (n +ℕ j))
      ( isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n)
        ( n +ℕ j)
        ( n≤n+j))
      ( dij +ℚ⁺ djk)
      ( map-isometry-leq-sequential-diagram-isometry-Metric-Space M i n Hi xᵢ)
      ( map-isometry-leq-sequential-diagram-isometry-Metric-Space M k n Hk xₖ)
      ( binary-tr
        ( neighborhood-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( dij +ℚ⁺ djk))
        ( compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( i)
          ( n)
          ( n +ℕ j)
          ( Hi)
          ( n≤n+j)
          ( i≤n+j)
          ( xᵢ))
        ( compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( k)
          ( n)
          ( n +ℕ j)
          ( Hk)
          ( n≤n+j)
          ( k≤n+j)
          ( xₖ))
        ( Nik+j))
    where
    i≤n+j : leq-ℕ i (n +ℕ j)
    i≤n+j = transitive-leq-ℕ i n (n +ℕ j) (leq-add-ℕ n j) Hi

    k≤n+j : leq-ℕ k (n +ℕ j)
    k≤n+j = transitive-leq-ℕ k n (n +ℕ j) (leq-add-ℕ n j) Hk

    j≤n+j : leq-ℕ j (n +ℕ j)
    j≤n+j = leq-add-ℕ' j n

    n≤n+j : leq-ℕ n (n +ℕ j)
    n≤n+j = leq-add-ℕ n j

    Nik+j :
      neighborhood-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (n +ℕ j))
        ( dij +ℚ⁺ djk)
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( i)
            ( n +ℕ j)
            ( i≤n+j))
          ( xᵢ))
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( k)
            ( n +ℕ j)
            ( k≤n+j))
          ( xₖ))
    Nik+j =
      triangular-neighborhood-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (n +ℕ j))
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( i)
            ( n +ℕ j)
            ( i≤n+j))
          ( xᵢ))
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( j)
            ( n +ℕ j)
            ( j≤n+j))
          ( xⱼ))
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n +ℕ j))
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( k)
            ( n +ℕ j)
            ( k≤n+j))
          ( xₖ))
        ( dij)
        ( djk)
        ( Njk (n +ℕ j) j≤n+j k≤n+j)
        ( Nij (n +ℕ j) i≤n+j j≤n+j)

  is-saturated-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space :
    is-saturated-Rational-Neighborhood-Relation
      ( neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space M)
  is-saturated-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    d (m , x) (n , y) sat-Nxy k Hm Hn =
    saturated-neighborhood-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
      ( d)
      ( _)
      ( _)
      ( λ d' → sat-Nxy d' k Hm Hn)

  pseudometric-structure-limit-sequential-diagram-isometry-Metric-Space :
    Pseudometric-Structure
      ( l2)
      ( type-Metric-Space
        ( tot-metric-space-sequential-diagram-isometry-Metric-Space M))
  pseudometric-structure-limit-sequential-diagram-isometry-Metric-Space =
    ( neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space M
    ,
      is-reflexive-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    ,
      is-symmetric-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    ,
      is-triangular-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space
    ,
      is-saturated-neighborhood-prop-limit-sequential-diagram-isometry-Metric-Space)
```

### The limit pseudometric space of a sequential diagram of isometries

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    Pseudometric-Space l1 l2
  pr1 pseudometric-space-limit-sequential-diagram-isometry-Metric-Space =
    type-Metric-Space
      ( tot-metric-space-sequential-diagram-isometry-Metric-Space M)
  pr2 pseudometric-space-limit-sequential-diagram-isometry-Metric-Space =
    pseudometric-structure-limit-sequential-diagram-isometry-Metric-Space M
```

### The limit metric space of a sequential diagram of isometries

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  metric-space-limit-sequential-diagram-isometry-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-space-limit-sequential-diagram-isometry-Metric-Space =
    metric-quotient-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
```

### The unit isometry into the limit pseudometric space

For any `n : ℕ`, the **unit isometry** `ιₙ : Mₙ → M∙` is the map
`xₙ ↦ (n , xₙ)`.

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  (n : ℕ)
  where

  map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    family-sequential-diagram-isometry-Metric-Space M n →
    type-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
  map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space x =
    (n , x)

  is-short-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    is-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
  is-short-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    d x y Nxy k H H' =
    tr
      ( neighborhood-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
        ( d)
        ( map-isometry-leq-sequential-diagram-isometry-Metric-Space M n k H x))
      ( ap
        ( λ K →
          map-isometry-leq-sequential-diagram-isometry-Metric-Space M n k K y)
        ( eq-is-prop (is-prop-leq-ℕ n k)))
      ( preserves-neighborhoods-map-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M n k H)
        ( d)
        ( x)
        ( y)
        ( Nxy))

  is-expansive-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    is-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
  is-expansive-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    d x y Nxy =
    Vxy
    where
      Vxy :
        neighborhood-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( d)
          ( x)
          ( y)
      Vxy =
        reflects-neighborhoods-map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( isometry-leq-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n)
            ( n)
            ( refl-leq-ℕ n))
          ( d)
          ( x)
          ( y)
          ( Nxy n (refl-leq-ℕ n) (refl-leq-ℕ n))

  is-isometry-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    is-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
  is-isometry-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    =
    is-isometry-is-expansive-map-is-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
      ( is-short-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
      ( is-expansive-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)

  seq-isometry-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
  seq-isometry-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    =
    ( map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    ,
      is-isometry-map-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space)
```

### The unit isometry into the limit metric space

For any `n : ℕ`, the **unit isometry** `Mₙ → M∞` is obtained by composition with
the
[unit map](metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces.md) of
metric quotients:

```text
      ιₙ       q
  Mₙ ----> M∙ ----> M∞
```

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  (n : ℕ)
  where

  seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space :
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( metric-space-limit-sequential-diagram-isometry-Metric-Space M)
  seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space =
    comp-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n))
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( pseudometric-metric-quotient-Pseudometric-Space
        ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M))
      ( isometry-unit-metric-quotient-Pseudometric-Space
        ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M))
      ( seq-isometry-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n))

  seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space :
    family-sequential-diagram-isometry-Metric-Space M n →
    type-Metric-Space
      ( metric-space-limit-sequential-diagram-isometry-Metric-Space M)
  seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( metric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space)
```

## Properties

### Similarity laws in the limit pseudometric space

For any `i j : ℕ` with `i ≤ j`, and for any `xᵢ : Mᵢ`, `ιᵢ xᵢ` and `ιⱼ (ϕᵢʲ xᵢ)`
are [similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) in
`M∙`.

In particular, for any `n : ℕ` and `xₙ : Mₙ`, `ιₙ xₙ ≍ ιₙ₊₁ (fₙ xₙ)` in `M∙`.

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  sim-map-isometry-leq-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    (i j : ℕ) →
    (H : leq-ℕ i j) →
    (x : family-sequential-diagram-isometry-Metric-Space M i) →
    sim-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( i , x)
      ( j , map-isometry-leq-sequential-diagram-isometry-Metric-Space M i j H x)
  sim-map-isometry-leq-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    i j H x d n Hi Hj =
    sim-eq-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( _)
      ( _)
      ( compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( i)
        ( j)
        ( n)
        ( H)
        ( Hj)
        ( Hi)
        ( x))
      ( d)

  sim-map-succ-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    (x : family-sequential-diagram-isometry-Metric-Space M n) →
    sim-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( n , x)
      ( succ-ℕ n ,
        seq-map-isometry-sequential-diagram-isometry-Metric-Space M n x)
  sim-map-succ-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
    n x =
    inv-tr
      ( λ y →
        sim-Pseudometric-Space
        ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
        ( n , x)
        ( succ-ℕ n , y))
      ( compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n)
        ( succ-leq-ℕ n)
        ( x))
      ( sim-map-isometry-leq-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
        ( n)
        ( succ-ℕ n)
        ( succ-leq-ℕ n)
        ( x))
```

### Coherence laws in the limit metric space

For any `i j : ℕ` with `i ≤ j`,

```text
  q ∘ ιᵢ ~ q ∘ ιⱼ ∘ ϕᵢʲ
```

in the space isometries `Mᵢ → M∞`.

In particular, for any `n : ℕ`

```text
  q ∘ ιₙ ~ q ∘ ιₙ₊₁ ∘ fₙ
```

in the space of isometries `Mₙ → M∞`.

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  compute-map-isometry-leq-metric-space-limit-sequential-diagram-isometry-Metric-Space :
    (i j : ℕ) →
    (H : leq-ℕ i j) →
    (x : family-sequential-diagram-isometry-Metric-Space M i) →
    seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space M i x ＝
    seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space M j
      ( map-isometry-leq-sequential-diagram-isometry-Metric-Space M i j H x)
  compute-map-isometry-leq-metric-space-limit-sequential-diagram-isometry-Metric-Space
    i j H x =
    eq-map-unit-metric-quotient-sim-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( _)
      ( _)
      ( sim-map-isometry-leq-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( i)
        ( j)
        ( H)
        ( x))

  is-coherent-seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space M n ~
    seq-map-metric-space-limit-sequential-diagram-isometry-Metric-Space
      ( M)
      ( succ-ℕ n) ∘
    seq-map-isometry-sequential-diagram-isometry-Metric-Space M n
  is-coherent-seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space
    n x =
    eq-map-unit-metric-quotient-sim-Pseudometric-Space
      ( pseudometric-space-limit-sequential-diagram-isometry-Metric-Space M)
      ( _)
      ( _)
      ( sim-map-succ-pseudometric-space-limit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n)
        ( x))
```

### Limit cocone under a sequential diagram of isometries

The sequence of unit maps into the metric limit induce a cocone

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯ ---> M∞
```

under `(M , f)`.

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  cocone-metric-space-limit-sequential-diagram-isometry-Metric-Space :
    cocone-sequential-diagram-isometry-Metric-Space
      ( M)
      ( metric-space-limit-sequential-diagram-isometry-Metric-Space M)
  pr1 cocone-metric-space-limit-sequential-diagram-isometry-Metric-Space =
    seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space M
  pr2 cocone-metric-space-limit-sequential-diagram-isometry-Metric-Space =
    is-coherent-seq-isometry-metric-space-limit-sequential-diagram-isometry-Metric-Space
      M
```
