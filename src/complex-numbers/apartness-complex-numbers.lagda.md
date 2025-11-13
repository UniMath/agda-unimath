# Apartness of complex numbers

```agda
module complex-numbers.apartness-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.large-apartness-relations
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.apartness-real-numbers
```

</details>

## Idea

Two [complex numbers](complex-numbers.complex-numbers.md) are
{{#concept "apart" Agda=apart-ℂ}} if their
[real](real-numbers.dedekind-real-numbers.md) parts are
[apart](real-numbers.apartness-real-numbers.md) [or](foundation.disjunction.md)
their imaginary parts are [apart].

## Definition

```agda
module _
  {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2)
  where

  apart-prop-ℂ : Prop (l1 ⊔ l2)
  apart-prop-ℂ =
    apart-prop-ℝ (re-ℂ z) (re-ℂ w) ∨ apart-prop-ℝ (im-ℂ z) (im-ℂ w)

  apart-ℂ : UU (l1 ⊔ l2)
  apart-ℂ = type-Prop apart-prop-ℂ
```

## Properties

### Apartness is antireflexive

```agda
abstract
  antireflexive-apart-ℂ : {l : Level} (z : ℂ l) → ¬ (apart-ℂ z z)
  antireflexive-apart-ℂ (a , b) =
    elim-disjunction
      ( empty-Prop)
      ( antireflexive-apart-ℝ a)
      ( antireflexive-apart-ℝ b)
```

### Apartness is symmetric

```agda
abstract
  symmetric-apart-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → apart-ℂ z w → apart-ℂ w z
  symmetric-apart-ℂ (a , b) (c , d) =
    map-disjunction symmetric-apart-ℝ symmetric-apart-ℝ
```

### Apartness is cotransitive

```agda
abstract
  cotransitive-apart-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    apart-ℂ x y → disjunction-type (apart-ℂ x z) (apart-ℂ z y)
  cotransitive-apart-ℂ x@(a , b) y@(c , d) z@(e , f) =
    elim-disjunction
      ( (apart-prop-ℂ x z) ∨ (apart-prop-ℂ z y))
      ( map-disjunction inl-disjunction inl-disjunction ∘
        cotransitive-apart-ℝ a c e)
      ( map-disjunction inr-disjunction inr-disjunction ∘
        cotransitive-apart-ℝ b d f)
```

### Apartness on the complex numbers is a large apartness relation

```agda
large-apartness-relation-ℂ : Large-Apartness-Relation _⊔_ ℂ
apart-prop-Large-Apartness-Relation large-apartness-relation-ℂ =
  apart-prop-ℂ
antirefl-Large-Apartness-Relation large-apartness-relation-ℂ =
  antireflexive-apart-ℂ
symmetric-Large-Apartness-Relation large-apartness-relation-ℂ =
  symmetric-apart-ℂ
cotransitive-Large-Apartness-Relation large-apartness-relation-ℂ =
  cotransitive-apart-ℂ
```
