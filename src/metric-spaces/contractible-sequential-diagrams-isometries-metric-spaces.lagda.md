# Contractible sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.contractible-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
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
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.colimits-of-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.expansive-maps-pseudometric-spaces
open import metric-spaces.functoriality-isometries-metric-quotients-of-pseudometric-spaces
open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.interval-isometries-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-metric-spaces
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
open import metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
[sequential diagram](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md)

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

is called
{{#concept "contractible" Disambiguation="sequential diagram of isometries"}} if
all the `fₙ`s are [equivalences](foundation.equivalences.md).

Considering
[colimit](metric-spaces.colimits-of-sequential-diagrams-isometries-metric-spaces.md)
diagram:

```text
     f₀       f₁       f₂      f∞
 M₀ ----> M₁ ----> M₂ ----> ⋯ ---> M∞
```

this is equivalent to the following conditions:

- the colimit isometry `ϕ₀∞ : M₀ → M∞` is an equivalence;
- for all `n : ℕ`, the colimit isometry `ϕₙ∞ : Mₙ → M∞` is an equivalence.

## Definitions

### Contractible sequential diagrams of isometries

```agda
module _
  { l1 l2 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  is-contr-sequential-diagram-isometry-Metric-Space : UU l1
  is-contr-sequential-diagram-isometry-Metric-Space =
    (n : ℕ) →
    is-equiv
      ( seq-map-isometry-sequential-diagram-isometry-Metric-Space M n)
```

### Sequential diagram with `M₀ ≃ M∞`

```agda
module _
  { l1 l2 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space :
    UU (l1 ⊔ l2)
  is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space =
    is-equiv
      ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( 0))
```

## Properties

### If the map `ϕ₀∞` an equivalence, then all the `ϕₙ∞`s are

```agda
module _
  { l1 l2 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( H : is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space M)
  where abstract

  seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    is-equiv
      ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n))
  seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
    zero-ℕ = H
  seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
    (succ-ℕ n) =
    is-equiv-is-section-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ n))
      ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
      ( seq-isometry-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( succ-ℕ n))
      ( ϕ∞ⁿ⁺¹)
      ( lemma-htpy-ϕ∞ⁿ⁺¹)
      where

      is-equiv-ϕ∞ⁿ :
        is-equiv
          ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n))
      is-equiv-ϕ∞ⁿ =
        seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
          ( n)

      ϕ∞ⁿ :
        isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ϕ∞ⁿ =
        isometry-inv-is-equiv-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-isometry-metric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n))
          ( is-equiv-ϕ∞ⁿ)

      ϕ∞ⁿ⁺¹ :
        isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( succ-ℕ n))
      ϕ∞ⁿ⁺¹ =
        comp-isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( succ-ℕ n))
          ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)
          ( ϕ∞ⁿ)

      lemma-htpy-ϕ∞ⁿ⁺¹ :
        ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ n)) ∘
        ( map-isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space
            ( M)
            ( succ-ℕ n))
          ( ϕ∞ⁿ⁺¹)) ~
        ( id)
      lemma-htpy-ϕ∞ⁿ⁺¹ x =
        inv
          ( is-coherent-seq-isometry-metric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M)
            ( n)
            ( _)) ∙
        is-section-map-inv-is-equiv
          ( is-equiv-ϕ∞ⁿ)
          ( x)
```

### If the map `ϕ₀∞` is an equivalence, then all the `fᵢ`s are

```agda
module _
  { l1 l2 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( H : is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space M)
  where abstract

  is-contr-sequential-diagram-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space :
    is-contr-sequential-diagram-isometry-Metric-Space M
  is-contr-sequential-diagram-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
    n =
    is-equiv-top-map-triangle
      ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n))
      ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( succ-ℕ n))
      ( seq-map-isometry-sequential-diagram-isometry-Metric-Space M n)
      ( is-coherent-seq-isometry-metric-space-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n))
      ( seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( H)
        ( succ-ℕ n))
      ( seq-is-equiv-is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space
        ( M)
        ( H)
        ( n))
```

### If all the `fᵢ`s are equivalences, then so is `ϕ₀∞`

If `(M , f)` is contractible, we can construct a
[cocone](metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces.md)

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯ ----> M₀
```

hence an isometry `ϕ∞⁰ : M∞ → M₀`

```text
     f₀       f₁       f₂      f∞       ϕ∞⁰
 M₀ ----> M₁ ----> M₂ ----> ⋯ ----> M∞ ----> M₀
```

such that `ϕ∞⁰ ∘ ϕ₀∞ ~ id` so `ϕ₀∞` is an equivalence.

```agda
module _
  { l1 l2 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( H : is-contr-sequential-diagram-isometry-Metric-Space M)
  where

  seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
  seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space zero-ℕ
    =
    id-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
  seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
    (succ-ℕ n) =
    comp-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ n))
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
      ( seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
        ( n))
      ( isometry-inv-is-equiv-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ n))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)
        ( H n))

  abstract
    coh-seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space :
      is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space
        ( M)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
        ( seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space)
    coh-seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
      zero-ℕ x =
      inv (is-retraction-map-inv-is-equiv (H zero-ℕ) x)
    coh-seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
      (succ-ℕ n) x =
      ap
        ( map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M
            ( succ-ℕ n))
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
          ( seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
            ( succ-ℕ n)))
          ( inv (is-retraction-map-inv-is-equiv (H (succ-ℕ n)) x))

  cocone-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space :
    cocone-sequential-diagram-isometry-Metric-Space
      ( M)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
  cocone-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space =
    ( seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
    , coh-seq-inv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
    )

  abstract
    is-equiv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space :
      is-equiv-zero-colimit-sequential-diagram-isometry-Metric-Space M
    is-equiv-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space
      =
      is-equiv-is-retraction-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
        ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
        ( seq-isometry-metric-space-colimit-sequential-diagram-isometry-Metric-Space
          ( M)
          ( 0))
        ( inv-isometry)
        ( is-section-map-inv-isometry)
      where

      inv-isometry :
        isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
      inv-isometry =
        isometry-exten-cocone-metric-space-colimit-sequential-diagram-isometry-Metric-Space
          ( M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
          ( cocone-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space)

      map-inv-isometry :
        map-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
      map-inv-isometry =
        map-isometry-Metric-Space
          ( metric-space-colimit-sequential-diagram-isometry-Metric-Space M)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
          ( inv-isometry)

      is-section-map-inv-isometry :
        is-section
          ( map-inv-isometry)
          ( seq-map-metric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M)
            ( 0))
      is-section-map-inv-isometry x =
        is-extension-exten-isometry-metric-quotient-Pseudometric-Space
          ( pseudometric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M))
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
          ( isometry-exten-cocone-pseudometric-space-colimit-sequential-diagram-isometry-Metric-Space
            ( M)
            ( seq-metric-space-sequential-diagram-isometry-Metric-Space M 0)
            ( cocone-zero-colimit-is-contr-sequential-diagram-isometry-Metric-Space))
          ( 0 , x)
```
