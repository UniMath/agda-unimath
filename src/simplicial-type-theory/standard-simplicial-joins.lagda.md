# Simplicial joins

```agda
module simplicial-type-theory.simplicial-joins where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
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
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.directed-relation-directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

We define the {{#concept "simplicial join"}} of two types `A ＊₂ B` as the
colimit of the diagram

```text
               A × B ----> B
                 |         ⋮
    id × 1₂ × id |         ⋮
                 ∨         ⋮
  A × B ---> A × 𝟚 × B     ⋮
    | id × 0₂ × id  ⋱      ⋮
    |                 ⋱    ⋮
    ∨                    ∨  ∨
    A ⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯> A ＊₂ B
```

Intuitively, we can understand `A ＊₂ B` as the universal type equipped with
edges `a →₂ b` for every `a : A` and `b : B`.

This construction satisfies the laws

- $𝟚 ≃ 1 ＊₂ 1$
- $Δⁿ⁺¹ ≃ Δⁿ⁺¹ ＊₂ 1 ≃ 1 ＊₂ Δⁿ⁺¹$
- $Λ²₀ ≃ 1 ＊₂ bool$
- $Λ²₂ ≃ bool ＊₂ 1$

## Postulates

### The standard simplicial join

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  postulate
    standard-simplicial-join : UU (l1 ⊔ l2)

    in-standard-simplicial-join : A → B → 𝟚 → standard-simplicial-join

    glue-source-standard-simplicial-join :
      (a : A) (b b' : B) →
      in-standard-simplicial-join a b 0₂ ＝ in-standard-simplicial-join a b' 0₂

    glue-target-standard-simplicial-join :
      (a a' : A) (b : B) →
      in-standard-simplicial-join a b 1₂ ＝ in-standard-simplicial-join a' b 1₂
```

It remains to define and postulate the induction principle of the simplicial
join.
