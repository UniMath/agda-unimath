# Directed joins

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-joins
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

We define the {{#concept "standard directed join"}} of two types `A *▵ B` as the
colimit of the diagram

```text
               A × B ----> B
                 |         ⋮
    id × 1▵ × id |         ⋮
                 ∨         ⋮
  A × B ---> A × Δ¹ × B     ⋮
    | id × 0▵ × id  ⋱      ⋮
    |                 ⋱    ⋮
    ∨                    ∨  ∨
    A ⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯> A *▵ B.
```

Equivalently, the standard directed join is the oriented pushout

```text
  A × B ------> B
    |           |
    |     ⇗     |
    ∨         ⌜ ∨
    A ------> A *▵ B.
```

Intuitively, we can understand `A *▵ B` as the universal type equipped with
edges `a →▵ b` for every `a : A` and `b : B`.

This construction satisfies the laws

- $Δ¹ ≃ 1 *▵ 1$

- $Δⁿ⁺¹ ≃ Δⁿ⁺¹ *▵ 1 ≃ 1 *▵ Δⁿ⁺¹$

- $Λ²₀ ≃ 1 *▵ bool$

- $Λ²₂ ≃ bool *▵ 1$

- $1 *▵ (-)$ is the directed cone

- $(-) *▵ 1$ is the simplicial cocone

## Postulates

### The standard directed join

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  postulate
    standard-directed-join : UU (I1 ⊔ l1 ⊔ l2)

    in-standard-directed-join : A → B → Δ¹ → standard-directed-join

    glue-source-standard-directed-join :
      (a : A) (b b' : B) →
      in-standard-directed-join a b 0▵ ＝ in-standard-directed-join a b' 0▵

    glue-target-standard-directed-join :
      (a a' : A) (b : B) →
      in-standard-directed-join a b 1▵ ＝ in-standard-directed-join a' b 1▵
```

> It remains to define and postulate the induction principle of the simplicial
> join.

## See also

- The simplicial pushout join
