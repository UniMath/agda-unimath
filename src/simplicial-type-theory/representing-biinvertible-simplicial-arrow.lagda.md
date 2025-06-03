# The representing biinvertible simplicial arrow

```agda
module simplicial-type-theory.representing-biinvertible-simplicial-arrow where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import reflection.erasing-equality

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-cubes
open import simplicial-type-theory.standard-simplices

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.recursion-principle-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

```text
  s ===== s
   ∧     / ∧
  l \ L / R \ r
     \ ∨     \
      t ===== t
```

## Postulates

```agda
postulate
  representing-biinvertible-simplicial-arrow : UU

  source-representing-biinvertible-simplicial-arrow :
    representing-biinvertible-simplicial-arrow

  target-representing-biinvertible-simplicial-arrow :
    representing-biinvertible-simplicial-arrow

  arrow-representing-biinvertible-simplicial-arrow :
    𝟚 → representing-biinvertible-simplicial-arrow

  arrow-left-inv-representing-biinvertible-simplicial-arrow :
    𝟚 → representing-biinvertible-simplicial-arrow

  arrow-right-inv-representing-biinvertible-simplicial-arrow :
    𝟚 → representing-biinvertible-simplicial-arrow

  left-2-cell-representing-biinvertible-simplicial-arrow :
    Δ 2 → representing-biinvertible-simplicial-arrow

  compute-0-left-2-cell-representing-biinvertible-simplicial-arrow :
    ( left-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((t , 0₂) , min-leq-𝟚)) ＝
    arrow-representing-biinvertible-simplicial-arrow

  compute-1-left-2-cell-representing-biinvertible-simplicial-arrow :
    ( left-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((t , t) , refl-leq-𝟚)) ＝
    id-simplicial-arrow target-representing-biinvertible-simplicial-arrow

  compute-2-left-2-cell-representing-biinvertible-simplicial-arrow :
    ( left-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((1₂ , t) , max-leq-𝟚)) ＝
    arrow-left-inv-representing-biinvertible-simplicial-arrow

  right-2-cell-representing-biinvertible-simplicial-arrow :
    Δ 2 → representing-biinvertible-simplicial-arrow

  compute-1-right-2-cell-representing-biinvertible-simplicial-arrow :
    ( right-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((t , t) , refl-leq-𝟚)) ＝
    id-simplicial-arrow source-representing-biinvertible-simplicial-arrow

  compute-0-right-2-cell-representing-biinvertible-simplicial-arrow :
    ( right-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((t , 0₂) , min-leq-𝟚)) ＝
    arrow-representing-biinvertible-simplicial-arrow

  compute-2-right-2-cell-representing-biinvertible-simplicial-arrow :
    ( right-2-cell-representing-biinvertible-simplicial-arrow) ∘
    ( λ t → ((1₂ , t) , max-leq-𝟚)) ＝
    arrow-representing-biinvertible-simplicial-arrow
```

## Definitions

```agda
source-arrow-representing-biinvertible-simplicial-arrow :
  arrow-representing-biinvertible-simplicial-arrow 0₂ ＝
  {! id-simplicial-arrow target-representing-biinvertible-simplicial-arrow 0₂ !}
  -- source-representing-biinvertible-simplicial-arrow
source-arrow-representing-biinvertible-simplicial-arrow =
  htpy-eq
    ( inv compute-0-left-2-cell-representing-biinvertible-simplicial-arrow)
    0₂ ∙
  {!   !} ∙
  htpy-eq compute-1-left-2-cell-representing-biinvertible-simplicial-arrow 0₂

target-arrow-representing-biinvertible-simplicial-arrow :
  arrow-representing-biinvertible-simplicial-arrow 1₂ ＝
  target-representing-biinvertible-simplicial-arrow
target-arrow-representing-biinvertible-simplicial-arrow = {!   !}

source-arrow-left-inv-representing-biinvertible-simplicial-arrow :
  arrow-left-inv-representing-biinvertible-simplicial-arrow 0₂ ＝
  target-representing-biinvertible-simplicial-arrow
source-arrow-left-inv-representing-biinvertible-simplicial-arrow = {!   !}

target-arrow-left-inv-representing-biinvertible-simplicial-arrow :
  arrow-left-inv-representing-biinvertible-simplicial-arrow 1₂ ＝
  source-representing-biinvertible-simplicial-arrow
target-arrow-left-inv-representing-biinvertible-simplicial-arrow = {!   !}

source-arrow-right-inv-representing-biinvertible-simplicial-arrow :
  arrow-right-inv-representing-biinvertible-simplicial-arrow 0₂ ＝
  target-representing-biinvertible-simplicial-arrow
source-arrow-right-inv-representing-biinvertible-simplicial-arrow = {!   !}

target-arrow-right-inv-representing-biinvertible-simplicial-arrow :
  arrow-right-inv-representing-biinvertible-simplicial-arrow 1₂ ＝
  source-representing-biinvertible-simplicial-arrow
target-arrow-right-inv-representing-biinvertible-simplicial-arrow = {!   !}
```
