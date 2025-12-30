# The density of rational numbers in proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.density-rationals-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.dense-subsets-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The [rational real numbers](real-numbers.rational-real-numbers.md) are
[dense](real-numbers.dense-subsets-real-numbers.md) in any
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md).

## Proof

```agda
abstract
  is-dense-subset-rational-proper-closed-interval-ℝ :
    {l1 l2 : Level} (l3 : Level) ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-dense-subset-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l3 [a,b])
      ( subtype-rational-ℝ ∘ pr1)
  is-dense-subset-rational-proper-closed-interval-ℝ
    l [a,b]@(a , b , a<b) (x , a≤x , x≤b) ε =
    let
      motive =
        ∃
          ( type-proper-closed-interval-ℝ l [a,b])
          ( λ (y , _) → neighborhood-prop-ℝ l ε x y ∧ subtype-rational-ℝ y)
      open do-syntax-trunc-Prop motive
    in
      elim-disjunction
        ( motive)
        ( λ a<x →
          do
            (δ , a+δ<x) ← exists-positive-rational-separation-le-ℝ a<x
            (q , q<x , Nδεxq) ←
              exists-rational-approximate-below-ℝ x (min-ℚ⁺ δ ε)
            intro-exists
              ( raise-real-ℚ l q ,
                transitive-leq-ℝ
                  ( a)
                  ( x -ℝ real-ℚ⁺ δ)
                  ( raise-real-ℚ l q)
                  ( leq-transpose-right-add-ℝ _ _ _
                    ( left-leq-real-bound-neighborhood-ℝ
                      ( δ)
                      ( x)
                      ( raise-real-ℚ l q)
                      ( weakly-monotonic-neighborhood-ℝ
                        ( x)
                        ( raise-real-ℚ l q)
                        ( min-ℚ⁺ δ ε)
                        ( δ)
                        ( leq-left-min-ℚ⁺ δ ε)
                        ( Nδεxq))))
                  ( leq-le-ℝ (le-transpose-left-add-ℝ _ _ _ a+δ<x)) ,
                transitive-leq-ℝ
                  ( raise-real-ℚ l q)
                  ( x)
                  ( b)
                  ( x≤b)
                  ( leq-le-ℝ (le-raise-real-is-in-lower-cut-ℝ l x q<x)))
              ( weakly-monotonic-neighborhood-ℝ
                  ( x)
                  ( raise-real-ℚ l q)
                  ( min-ℚ⁺ δ ε)
                  ( ε)
                  ( leq-right-min-ℚ⁺ δ ε)
                  ( Nδεxq) ,
                q ,
                is-rational-raise-real-ℚ l q))
        ( λ x<b →
          do
            (δ , x+δ<b) ← exists-positive-rational-separation-le-ℝ x<b
            (q , x<q , Nδεxq) ←
              exists-rational-approximate-above-ℝ x (min-ℚ⁺ δ ε)
            intro-exists
              ( raise-real-ℚ l q ,
                transitive-leq-ℝ
                  ( a)
                  ( x)
                  ( raise-real-ℚ l q)
                  ( leq-le-ℝ (le-raise-real-is-in-upper-cut-ℝ x l x<q))
                  ( a≤x) ,
                transitive-leq-ℝ
                  ( raise-real-ℚ l q)
                  ( x +ℝ real-ℚ⁺ δ)
                  ( b)
                  ( leq-le-ℝ x+δ<b)
                  ( right-leq-real-bound-neighborhood-ℝ
                    ( δ)
                    ( x)
                    ( raise-real-ℚ l q)
                    ( weakly-monotonic-neighborhood-ℝ
                      ( x)
                      ( raise-real-ℚ l q)
                      ( min-ℚ⁺ δ ε)
                      ( δ)
                      ( leq-left-min-ℚ⁺ δ ε)
                      ( Nδεxq))))
              ( weakly-monotonic-neighborhood-ℝ
                  ( x)
                  ( raise-real-ℚ l q)
                  ( min-ℚ⁺ δ ε)
                  ( ε)
                  ( leq-right-min-ℚ⁺ δ ε)
                  ( Nδεxq) ,
                q ,
                is-rational-raise-real-ℚ l q))
        ( cotransitive-le-ℝ a b x a<b)
```
