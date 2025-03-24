# The maximum of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers.maximum-upper-dedekind-real-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.maximum-rational-numbers funext univalence truncations
open import elementary-number-theory.rational-numbers funext univalence truncations
open import elementary-number-theory.strict-inequality-rational-numbers funext univalence truncations

open import foundation.cartesian-product-types funext univalence
open import foundation.conjunction funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.disjunction funext univalence truncations
open import foundation.existential-quantification funext univalence truncations
open import foundation.function-types funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.inhabited-types funext univalence truncations
open import foundation.intersections-subtypes funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.powersets funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import logic.functoriality-existential-quantification funext univalence truncations

open import order-theory.large-join-semilattices funext univalence truncations
open import order-theory.least-upper-bounds-large-posets funext univalence truncations

open import real-numbers.inequality-upper-dedekind-real-numbers funext univalence truncations
open import real-numbers.upper-dedekind-real-numbers funext univalence truncations
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="binary, upper Dedekind real numbers" Agda=binary-max-upper-ℝ WD="maximum" WDID=Q10578722}}
of two
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md) `x`
and `y` is an upper Dedekind real number with cut equal to the intersection of
the cuts of `x` and `y`.

## Definition

### Binary maximum

```agda
module _
  {l1 l2 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2)
  where

  cut-binary-max-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-max-upper-ℝ = intersection-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)

  abstract
    max-inhabitants-in-binary-max-upper-ℝ :
      (p q : ℚ) → (is-in-cut-upper-ℝ x p) → (is-in-cut-upper-ℝ y q) →
      is-in-subtype cut-binary-max-upper-ℝ (max-ℚ p q)
    max-inhabitants-in-binary-max-upper-ℝ p q x<p y<q =
      is-in-cut-leq-ℚ-upper-ℝ x p (max-ℚ p q) (leq-left-max-ℚ p q) x<p ,
      is-in-cut-leq-ℚ-upper-ℝ y q (max-ℚ p q) (leq-right-max-ℚ p q) y<q

    is-inhabited-cut-binary-max-upper-ℝ : exists ℚ cut-binary-max-upper-ℝ
    is-inhabited-cut-binary-max-upper-ℝ =
      map-binary-exists
        ( is-in-subtype cut-binary-max-upper-ℝ)
        ( max-ℚ)
        ( max-inhabitants-in-binary-max-upper-ℝ)
        ( is-inhabited-cut-upper-ℝ x)
        ( is-inhabited-cut-upper-ℝ y)

    forward-implication-is-rounded-cut-binary-max-upper-ℝ :
      (q : ℚ) →
      is-in-subtype cut-binary-max-upper-ℝ q →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-max-upper-ℝ p)
    forward-implication-is-rounded-cut-binary-max-upper-ℝ q (x<q , y<q) =
      map-binary-exists
        ( λ p → le-ℚ p q × is-in-subtype cut-binary-max-upper-ℝ p)
        ( max-ℚ)
        ( λ px py (px<q , x<px) (py<q , y<py) →
          le-max-le-both-ℚ q px py px<q py<q ,
          max-inhabitants-in-binary-max-upper-ℝ px py x<px y<py)
        ( forward-implication (is-rounded-cut-upper-ℝ x q) x<q)
        ( forward-implication (is-rounded-cut-upper-ℝ y q) y<q)

    backward-implication-is-rounded-cut-binary-max-upper-ℝ :
      (q : ℚ) →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-max-upper-ℝ p) →
      is-in-subtype cut-binary-max-upper-ℝ q
    backward-implication-is-rounded-cut-binary-max-upper-ℝ q =
      elim-exists
        ( cut-binary-max-upper-ℝ q)
        ( λ p (p<q , x<p , y<p) →
          backward-implication
            ( is-rounded-cut-upper-ℝ x q)
            ( intro-exists p (p<q , x<p)) ,
          backward-implication
            ( is-rounded-cut-upper-ℝ y q)
            ( intro-exists p (p<q , y<p)))

    is-rounded-cut-binary-max-upper-ℝ :
      (q : ℚ) →
      is-in-subtype cut-binary-max-upper-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-max-upper-ℝ p)
    is-rounded-cut-binary-max-upper-ℝ q =
      forward-implication-is-rounded-cut-binary-max-upper-ℝ q ,
      backward-implication-is-rounded-cut-binary-max-upper-ℝ q

  binary-max-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  binary-max-upper-ℝ =
    cut-binary-max-upper-ℝ ,
    is-inhabited-cut-binary-max-upper-ℝ ,
    is-rounded-cut-binary-max-upper-ℝ
```

## Properties

### The binary maximum is a least upper bound

```agda
  is-least-binary-upper-bound-binary-max-upper-ℝ :
    is-least-binary-upper-bound-Large-Poset
      ( upper-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-max-upper-ℝ)
  is-least-binary-upper-bound-binary-max-upper-ℝ z =
    is-greatest-binary-lower-bound-intersection-subtype
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)
      ( cut-upper-ℝ z)
```

### The upper Dedekind reals form a large join-semilattice

```agda
has-joins-upper-ℝ : has-joins-Large-Poset upper-ℝ-Large-Poset
join-has-joins-Large-Poset has-joins-upper-ℝ = binary-max-upper-ℝ
is-least-binary-upper-bound-join-has-joins-Large-Poset has-joins-upper-ℝ =
  is-least-binary-upper-bound-binary-max-upper-ℝ

is-large-join-semilattice-upper-ℝ :
  is-large-join-semilattice-Large-Poset upper-ℝ-Large-Poset
has-joins-is-large-join-semilattice-Large-Poset
  is-large-join-semilattice-upper-ℝ = has-joins-upper-ℝ
has-bottom-element-is-large-join-semilattice-Large-Poset
  is-large-join-semilattice-upper-ℝ = has-bottom-element-upper-ℝ

upper-ℝ-Large-Join-Semilattice : Large-Join-Semilattice lsuc _⊔_
large-poset-Large-Join-Semilattice upper-ℝ-Large-Join-Semilattice =
  upper-ℝ-Large-Poset
is-large-join-semilattice-Large-Join-Semilattice
  upper-ℝ-Large-Join-Semilattice = is-large-join-semilattice-upper-ℝ
```
