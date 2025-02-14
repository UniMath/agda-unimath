# Addition of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.addition-upper-dedekind-real-numbers
```

</details>

## Idea

The sum of two
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) is
is a Dedekind real number whose lower cut (upper cut) is the
the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
their lower (upper) cuts.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-add-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-add-ℝ = add-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-add-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-add-ℝ = add-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  is-disjoint-lower-upper-add-ℝ :
    is-disjoint-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
  is-disjoint-lower-upper-add-ℝ p (p<x+y , x+y<p) =
    do
      ((px , py) , px<x , py<y , p=px+py) ← p<x+y
      ((qx , qy) , x<qx , y<qy , p=qx+qy) ← x+y<p
      irreflexive-le-ℚ
        ( p)
        ( binary-tr
          ( le-ℚ)
          ( inv (p=px+py))
          ( inv (p=qx+qy))
          ( preserves-le-add-ℚ
            { px}
            { qx}
            { py}
            { qy}
            (le-lower-upper-cut-ℝ x px qx px<x x<qx)
            (le-lower-upper-cut-ℝ y py qy py<y y<qy)))
    where open do-syntax-trunc-Prop empty-Prop

  is-located-lower-upper-add-ℝ :
    is-located-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
  is-located-lower-upper-add-ℝ = {!   !}

  add-ℝ : ℝ (l1 ⊔ l2)
  pr1 add-ℝ = lower-real-add-ℝ
  pr1 (pr2 add-ℝ) = upper-real-add-ℝ
  pr1 (pr2 (pr2 add-ℝ)) = is-disjoint-lower-upper-add-ℝ
  pr2 (pr2 (pr2 add-ℝ)) = is-located-lower-upper-add-ℝ
```
