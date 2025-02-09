# Inequality on the lower Dedekind real numbers

```agda
module real-numbers.inequality-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="lower Dedekind real numbers" Agda=leq-lower-ℝ}} on
the [lower real numbers](real-numbers.lower-dedekind-real-numbers.md) is defined as the
cut of one being a subset of the cut of the other.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  leq-lower-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-lower-ℝ-Prop = leq-prop-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)
```

### Inequality on lower Dedekind reals is a large poset

```agda
lower-ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
lower-ℝ-Large-Preorder = powerset-Large-Preorder ℚ

lower-ℝ-Large-Poset : Large-Poset lsuc _⊔_
lower-ℝ-Large-Poset = powerset-Large-Poset ℚ
```

## References

{{#bibliography}}
