# Apartness of real numbers

```agda
module real-numbers.apartness-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.disjunction
open import foundation.empty-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Two real numbers are [apart](foundation.apartness-relations.md) if one
is strictly less than the other.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  apart-ℝ-Prop : Prop (l1 ⊔ l2)
  apart-ℝ-Prop = le-ℝ-Prop x y ∨ le-ℝ-Prop y x

  apart-ℝ : UU (l1 ⊔ l2)
  apart-ℝ = type-Prop apart-ℝ-Prop
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
  elim-disjunction (apart-ℝ-Prop y x) inr-disjunction inl-disjunction
```

### Apartness is cotransitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  cotransitive-apart-ℝ : is-cotransitive apart-ℝ-Prop

```
