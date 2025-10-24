# Apartness of real numbers

```agda
module real-numbers.apartness-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.coproduct-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.large-apartness-relations
open import foundation.large-binary-relations
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Two [real numbers](real-numbers.dedekind-real-numbers.md) are
[apart](foundation.large-apartness-relations.md) if one is
[strictly less](real-numbers.strict-inequality-real-numbers.md) than the other.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  apart-prop-ℝ : Prop (l1 ⊔ l2)
  apart-prop-ℝ = le-prop-ℝ x y ∨ le-prop-ℝ y x

  apart-ℝ : UU (l1 ⊔ l2)
  apart-ℝ = type-Prop apart-prop-ℝ
```

## Properties

### Apartness is antireflexive

```agda
antireflexive-apart-ℝ : {l : Level} → (x : ℝ l) → ¬ (apart-ℝ x x)
antireflexive-apart-ℝ x =
  elim-disjunction empty-Prop (irreflexive-le-ℝ x) (irreflexive-le-ℝ x)
```

### Apartness is symmetric

```agda
symmetric-apart-ℝ :
  {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → apart-ℝ x y → apart-ℝ y x
symmetric-apart-ℝ x y =
  elim-disjunction (apart-prop-ℝ y x) inr-disjunction inl-disjunction
```

### Apartness is cotransitive

```agda
cotransitive-apart-ℝ : is-cotransitive-Large-Relation-Prop ℝ apart-prop-ℝ
cotransitive-apart-ℝ x y z =
  elim-disjunction
    ( apart-prop-ℝ x z ∨ apart-prop-ℝ z y)
    ( λ x<y →
      map-disjunction
        ( inl-disjunction)
        ( inl-disjunction)
        ( cotransitive-le-ℝ x y z x<y))
    ( λ y<x →
      elim-disjunction
        ( apart-prop-ℝ x z ∨ apart-prop-ℝ z y)
        ( inr-disjunction ∘ inr-disjunction)
        ( inl-disjunction ∘ inr-disjunction)
        ( cotransitive-le-ℝ y x z y<x))
```

### Apartness on the reals is a large apartness relation

```agda
large-apartness-relation-ℝ : Large-Apartness-Relation _⊔_ ℝ
apart-prop-Large-Apartness-Relation large-apartness-relation-ℝ =
  apart-prop-ℝ
antirefl-Large-Apartness-Relation large-apartness-relation-ℝ =
  antireflexive-apart-ℝ
symmetric-Large-Apartness-Relation large-apartness-relation-ℝ =
  symmetric-apart-ℝ
cotransitive-Large-Apartness-Relation large-apartness-relation-ℝ =
  cotransitive-apart-ℝ
```

### Apart real numbers are nonequal

```agda
nonequal-apart-ℝ : {l : Level} (x y : ℝ l) → apart-ℝ x y → x ≠ y
nonequal-apart-ℝ x y =
  nonequal-apart-Large-Apartness-Relation large-apartness-relation-ℝ
```

### Zero is apart from one

```agda
apart-zero-one-ℝ : apart-ℝ zero-ℝ one-ℝ
apart-zero-one-ℝ = unit-trunc-Prop (inl le-zero-one-ℝ)
```

### Zero is not equal to one

```agda
zero-is-not-one-ℝ : zero-ℝ ≠ one-ℝ
zero-is-not-one-ℝ = nonequal-apart-ℝ zero-ℝ one-ℝ apart-zero-one-ℝ
```
