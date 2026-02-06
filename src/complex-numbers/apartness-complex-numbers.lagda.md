# Apartness of complex numbers

```agda
module complex-numbers.apartness-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.large-apartness-relations
open import foundation.negation
open import foundation.propositions
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import real-numbers.apartness-real-numbers
```

</details>

## Idea

Two [complex numbers](complex-numbers.complex-numbers.md) are
{{#concept "apart" Disambiguation="complex numbers" Agda=apart-ℂ}} if their
[real](real-numbers.dedekind-real-numbers.md) parts are
[apart](real-numbers.apartness-real-numbers.md) [or](foundation.disjunction.md)
their imaginary parts are apart.

## Definition

```agda
module _
  {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2)
  where

  apart-prop-ℂ : Prop (l1 ⊔ l2)
  apart-prop-ℂ =
    (apart-prop-ℝ (re-ℂ z) (re-ℂ w)) ∨ (apart-prop-ℝ (im-ℂ z) (im-ℂ w))

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

### The apartness relation of complex numbers at a particular universe level

```agda
apartness-relation-ℂ : (l : Level) → Apartness-Relation l (ℂ l)
apartness-relation-ℂ l =
  apartness-relation-Large-Apartness-Relation large-apartness-relation-ℂ l
```

### If two complex numbers at the same universe level are not apart, they are equal

```agda
abstract
  is-tight-apartness-relation-ℂ :
    (l : Level) → is-tight-Apartness-Relation (apartness-relation-ℂ l)
  is-tight-apartness-relation-ℂ l (a +iℂ b) (c +iℂ d) ¬a+ib#c+id =
    eq-ℂ
      ( is-tight-apartness-relation-ℝ l a c (¬a+ib#c+id ∘ inl-disjunction))
      ( is-tight-apartness-relation-ℝ l b d (¬a+ib#c+id ∘ inr-disjunction))

tight-apartness-relation-ℂ : (l : Level) → Tight-Apartness-Relation l (ℂ l)
tight-apartness-relation-ℂ l =
  ( apartness-relation-ℂ l ,
    is-tight-apartness-relation-ℂ l)
```

### Apartness is preserved by similarity

```agda
abstract
  apart-right-sim-ℂ :
    {l1 l2 l3 : Level} →
    (z : ℂ l1) (x : ℂ l2) (y : ℂ l3) →
    sim-ℂ x y → apart-ℂ z x → apart-ℂ z y
  apart-right-sim-ℂ (a +iℂ b) (c +iℂ d) (e +iℂ f) (c~e , d~f) =
    map-disjunction
      ( apart-right-sim-ℝ a c e c~e)
      ( apart-right-sim-ℝ b d f d~f)
```
