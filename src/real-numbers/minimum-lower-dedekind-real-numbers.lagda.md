# The minimum of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers.minimum-lower-dedekind-real-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-rational-numbers funext univalence truncations
open import elementary-number-theory.rational-numbers funext univalence truncations
open import elementary-number-theory.strict-inequality-rational-numbers funext univalence truncations

open import foundation.cartesian-product-types funext univalence
open import foundation.conjunction funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.existential-quantification funext univalence truncations
open import foundation.intersections-subtypes funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import logic.functoriality-existential-quantification funext univalence truncations

open import order-theory.greatest-lower-bounds-large-posets funext univalence truncations
open import order-theory.large-meet-semilattices funext univalence truncations
open import order-theory.lower-bounds-large-posets funext univalence truncations

open import real-numbers.inequality-lower-dedekind-real-numbers funext univalence truncations
open import real-numbers.lower-dedekind-real-numbers funext univalence truncations
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="binary, lower Dedekind real numbers" Agda=binary-min-lower-ℝ WD="minimum" WDID=Q10585806}}
of two
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md) `x`
and `y` is a lower Dedekind real number with cut equal to the intersection of
the cuts of `x` and `y`.

The minimum of a family of lower Dedekind real numbers is not always a lower
Dedekind real number. For example, the minimum of all lower Dedekind real
numbers would have an empty cut and would fail to be inhabited.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-binary-min-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-min-lower-ℝ = intersection-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  abstract
    min-inhabitants-in-binary-min-lower-ℝ :
      (p q : ℚ) → (is-in-cut-lower-ℝ x p) → (is-in-cut-lower-ℝ y q) →
      is-in-subtype cut-binary-min-lower-ℝ (min-ℚ p q)
    min-inhabitants-in-binary-min-lower-ℝ p q p<x q<y =
      is-in-cut-leq-ℚ-lower-ℝ x (min-ℚ p q) p (leq-left-min-ℚ p q) p<x ,
          is-in-cut-leq-ℚ-lower-ℝ y (min-ℚ p q) q (leq-right-min-ℚ p q) q<y

    is-inhabited-cut-binary-min-lower-ℝ : exists ℚ cut-binary-min-lower-ℝ
    is-inhabited-cut-binary-min-lower-ℝ =
      map-binary-exists
        ( is-in-subtype cut-binary-min-lower-ℝ)
        ( min-ℚ)
        ( min-inhabitants-in-binary-min-lower-ℝ)
        ( is-inhabited-cut-lower-ℝ x)
        ( is-inhabited-cut-lower-ℝ y)

    forward-implication-is-rounded-cut-binary-min-lower-ℝ :
      (q : ℚ) →
      is-in-subtype cut-binary-min-lower-ℝ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-min-lower-ℝ r)
    forward-implication-is-rounded-cut-binary-min-lower-ℝ q (q<x , q<y) =
      map-binary-exists
        ( λ r → le-ℚ q r × is-in-subtype cut-binary-min-lower-ℝ r)
        ( min-ℚ)
        ( λ rx ry (q<rx , rx<x) (q<ry , ry<y) →
          le-min-le-both-ℚ q rx ry q<rx q<ry ,
          min-inhabitants-in-binary-min-lower-ℝ rx ry rx<x ry<y)
        ( forward-implication (is-rounded-cut-lower-ℝ x q) q<x)
        ( forward-implication (is-rounded-cut-lower-ℝ y q) q<y)

    backward-implication-is-rounded-cut-binary-min-lower-ℝ :
      (q : ℚ) →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-min-lower-ℝ r) →
      is-in-subtype cut-binary-min-lower-ℝ q
    backward-implication-is-rounded-cut-binary-min-lower-ℝ q =
      elim-exists
        ( cut-binary-min-lower-ℝ q)
        ( λ r (q<r , q<x , q<y) →
          backward-implication
            ( is-rounded-cut-lower-ℝ x q)
            ( intro-exists r (q<r , q<x)) ,
          backward-implication
            ( is-rounded-cut-lower-ℝ y q)
            ( intro-exists r (q<r , q<y)))

    is-rounded-cut-binary-min-lower-ℝ :
      (q : ℚ) →
      is-in-subtype cut-binary-min-lower-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-min-lower-ℝ r)
    is-rounded-cut-binary-min-lower-ℝ q =
      forward-implication-is-rounded-cut-binary-min-lower-ℝ q ,
      backward-implication-is-rounded-cut-binary-min-lower-ℝ q

  binary-min-lower-ℝ : lower-ℝ (l1 ⊔ l2)
  binary-min-lower-ℝ =
    cut-binary-min-lower-ℝ ,
    is-inhabited-cut-binary-min-lower-ℝ ,
    is-rounded-cut-binary-min-lower-ℝ
```

## Properties

### The binary minimum of lower Dedekind real numbers is a greatest lower bound

```agda
  is-greatest-binary-lower-bound-binary-min-lower-ℝ :
    is-greatest-binary-lower-bound-Large-Poset
      lower-ℝ-Large-Poset
      x
      y
      binary-min-lower-ℝ
  is-greatest-binary-lower-bound-binary-min-lower-ℝ z =
    is-greatest-binary-lower-bound-intersection-subtype
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      ( cut-lower-ℝ z)
```

### The lower Dedekind real numbers form a large meet-semilattice

```agda
has-meets-lower-ℝ : has-meets-Large-Poset lower-ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-lower-ℝ = binary-min-lower-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset has-meets-lower-ℝ =
  is-greatest-binary-lower-bound-binary-min-lower-ℝ

is-large-meet-semilattice-lower-ℝ :
  is-large-meet-semilattice-Large-Poset lower-ℝ-Large-Poset
has-meets-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-lower-ℝ = has-meets-lower-ℝ
has-top-element-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-lower-ℝ = has-top-element-lower-ℝ

lower-ℝ-Large-Meet-Semilattice : Large-Meet-Semilattice lsuc _⊔_
large-poset-Large-Meet-Semilattice lower-ℝ-Large-Meet-Semilattice =
  lower-ℝ-Large-Poset
is-large-meet-semilattice-Large-Meet-Semilattice
  lower-ℝ-Large-Meet-Semilattice = is-large-meet-semilattice-lower-ℝ
```
