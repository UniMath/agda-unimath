# The representing biinvertible arrow

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.representing-biinvertible-arrow
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.cubes I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I
open import simplicial-type-theory.standard-simplices I

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

> This definition should be reconsidered.

```agda
postulate
  representing-biinvertible-arrow▵ : UU

  source-representing-biinvertible-arrow▵ :
    representing-biinvertible-arrow▵

  target-representing-biinvertible-arrow▵ :
    representing-biinvertible-arrow▵

  arrow-representing-biinvertible-arrow▵ :
    Δ¹ → representing-biinvertible-arrow▵

  arrow-left-inv-representing-biinvertible-arrow▵ :
    Δ¹ → representing-biinvertible-arrow▵

  arrow-right-inv-representing-biinvertible-arrow▵ :
    Δ¹ → representing-biinvertible-arrow▵

  left-2-cell-representing-biinvertible-arrow▵ :
    Δ 2 → representing-biinvertible-arrow▵

  compute-0-left-2-cell-representing-biinvertible-arrow▵ :
    ( left-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((t , 0▵) , min-leq-Δ¹)) ＝
    arrow-representing-biinvertible-arrow▵

  compute-1-left-2-cell-representing-biinvertible-arrow▵ :
    ( left-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((t , t) , refl-leq-Δ¹)) ＝
    id-arrow▵ target-representing-biinvertible-arrow▵

  compute-2-left-2-cell-representing-biinvertible-arrow▵ :
    ( left-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((1▵ , t) , max-leq-Δ¹)) ＝
    arrow-left-inv-representing-biinvertible-arrow▵

  right-2-cell-representing-biinvertible-arrow▵ :
    Δ 2 → representing-biinvertible-arrow▵

  compute-1-right-2-cell-representing-biinvertible-arrow▵ :
    ( right-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((t , t) , refl-leq-Δ¹)) ＝
    id-arrow▵ source-representing-biinvertible-arrow▵

  compute-0-right-2-cell-representing-biinvertible-arrow▵ :
    ( right-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((t , 0▵) , min-leq-Δ¹)) ＝
    arrow-representing-biinvertible-arrow▵

  compute-2-right-2-cell-representing-biinvertible-arrow▵ :
    ( right-2-cell-representing-biinvertible-arrow▵) ∘
    ( λ t → ((1▵ , t) , max-leq-Δ¹)) ＝
    arrow-representing-biinvertible-arrow▵
```

## Definitions

```text
source-arrow-representing-biinvertible-arrow▵ :
  arrow-representing-biinvertible-arrow▵ 0▵ ＝
  {! id-arrow▵ target-representing-biinvertible-arrow▵ 0▵ !}
  -- source-representing-biinvertible-arrow▵
source-arrow-representing-biinvertible-arrow▵ =
  htpy-eq
    ( inv compute-0-left-2-cell-representing-biinvertible-arrow▵)
    0▵ ∙
  {!   !} ∙
  htpy-eq compute-1-left-2-cell-representing-biinvertible-arrow▵ 0▵

target-arrow-representing-biinvertible-arrow▵ :
  arrow-representing-biinvertible-arrow▵ 1▵ ＝
  target-representing-biinvertible-arrow▵
target-arrow-representing-biinvertible-arrow▵ = {!   !}

source-arrow-left-inv-representing-biinvertible-arrow▵ :
  arrow-left-inv-representing-biinvertible-arrow▵ 0▵ ＝
  target-representing-biinvertible-arrow▵
source-arrow-left-inv-representing-biinvertible-arrow▵ = {!   !}

target-arrow-left-inv-representing-biinvertible-arrow▵ :
  arrow-left-inv-representing-biinvertible-arrow▵ 1▵ ＝
  source-representing-biinvertible-arrow▵
target-arrow-left-inv-representing-biinvertible-arrow▵ = {!   !}

source-arrow-right-inv-representing-biinvertible-arrow▵ :
  arrow-right-inv-representing-biinvertible-arrow▵ 0▵ ＝
  target-representing-biinvertible-arrow▵
source-arrow-right-inv-representing-biinvertible-arrow▵ = {!   !}

target-arrow-right-inv-representing-biinvertible-arrow▵ :
  arrow-right-inv-representing-biinvertible-arrow▵ 1▵ ＝
  source-representing-biinvertible-arrow▵
target-arrow-right-inv-representing-biinvertible-arrow▵ = {!   !}
```
