# Inequality on the upper Dedekind real numbers

```agda
module real-numbers.inequality-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.rational-upper-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="upper Dedekind real numbers" Agda=leq-upper-ℝ}} on
the [upper real numbers](real-numbers.upper-dedekind-real-numbers.md) is defined as the
cut of the second being a subset of the cut of the first.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  leq-upper-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-upper-ℝ-Prop = leq-prop-subtype (cut-upper-ℝ y) (cut-upper-ℝ x)

  leq-upper-ℝ : UU (l1 ⊔ l2)
  leq-upper-ℝ = type-Prop leq-upper-ℝ-Prop
```

## Properties

### Inequality on upper Dedekind reals is a large poset

```agda
upper-ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
upper-ℝ-Large-Preorder = powerset-Large-Preorder ℚ

upper-ℝ-Large-Poset : Large-Poset lsuc _⊔_
upper-ℝ-Large-Poset = powerset-Large-Poset ℚ
```

### The canonical map from the rational numbers to the upper reals preserves inequality

```agda
preserves-leq-upper-real-ℚ :
  (p q : ℚ) → leq-ℚ p q → leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q)
preserves-leq-upper-real-ℚ p q p≤q r = concatenate-leq-le-ℚ p q r p≤q

reflects-leq-upper-real-ℚ :
  (p q : ℚ) → leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q) → leq-ℚ p q
reflects-leq-upper-real-ℚ p q q<r→p<r with decide-le-leq-ℚ q p
... | inr p≤q = p≤q
... | inl q<p = ex-falso (irreflexive-le-ℚ p (q<r→p<r p q<p))

iff-leq-upper-real-ℚ :
  (p q : ℚ) → leq-ℚ p q ↔ leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q)
pr1 (iff-leq-upper-real-ℚ p q) = preserves-leq-upper-real-ℚ p q
pr2 (iff-leq-upper-real-ℚ p q) = reflects-leq-upper-real-ℚ p q
```
