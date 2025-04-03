# The distance between real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.distance-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositional-truncations
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.absolute-value-real-numbers
open import real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers
```

</details>

## Idea

The distance between two [real numbers](real-numbers.dedekind-real-numbers.md)
is the [absolute value](real-numbers.absolute-value-real-numbers.md) of their
[difference](real-numbers.difference-real-numbers.md).

## Definition

```agda
dist-ℝ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → ℝ (l1 ⊔ l2)
dist-ℝ x y = abs-ℝ (x -ℝ y)
```

### The distance function is commutative

```agda
abstract
  commutative-dist-ℝ :
    {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → dist-ℝ x y ＝ dist-ℝ y x
  commutative-dist-ℝ x y =
    inv (abs-neg-ℝ _) ∙ ap abs-ℝ (distributive-neg-diff-ℝ x y)
```

### Relationship to the metric space of real numbers

```agda
opaque
  unfolding add-ℝ

  diff-bound-neighborhood-leq-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y →
    leq-ℝ (x -ℝ y) (real-ℚ (rational-ℚ⁺ d))
  diff-bound-neighborhood-leq-ℝ d⁺@(d , _) x y (H , K) =
    leq-transpose-right-add-ℝ
      ( x)
      ( real-ℚ d)
      ( y)
      ( λ q q<x →
        tr
          ( λ z → is-in-lower-cut-ℝ z q)
          ( commutative-add-ℝ y (real-ℚ d))
          ( transpose-diff-is-in-lower-cut-ℝ
            ( y)
            ( q)
            ( d)
            ( K
              ( q -ℚ d)
              ( inv-tr (is-in-lower-cut-ℝ x) (is-section-diff-ℚ d q) q<x))))

  reversed-diff-bound-neighborhood-leq-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y →
    leq-ℝ (y -ℝ x) (real-ℚ (rational-ℚ⁺ d))
  reversed-diff-bound-neighborhood-leq-ℝ d x y H =
    diff-bound-neighborhood-leq-ℝ d y x (is-symmetric-premetric-leq-ℝ d x y H)

  leq-dist-neighborhood-leq-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y →
    leq-ℝ (dist-ℝ x y) (real-ℚ (rational-ℚ⁺ d))
  leq-dist-neighborhood-leq-ℝ d⁺@(d , _) x y H =
    leq-abs-leq-leq-neg-ℝ
      ( x -ℝ y)
      ( real-ℚ d)
      ( diff-bound-neighborhood-leq-ℝ d⁺ x y H)
      ( inv-tr
        ( λ z → leq-ℝ z (real-ℚ d))
        ( distributive-neg-diff-ℝ _ _)
        ( reversed-diff-bound-neighborhood-leq-ℝ d⁺ x y H))

  lower-neighborhood-leq-diff-bound-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    leq-ℝ (x -ℝ y) (real-ℚ (rational-ℚ⁺ d)) →
    is-in-lower-neighborhood-leq-ℝ d y x
  lower-neighborhood-leq-diff-bound-ℝ d⁺@(d , _) x y x-y≤d q q+d<x =
    is-in-lower-cut-le-real-ℚ
      ( q)
      ( y)
      ( concatenate-le-leq-ℝ
        ( real-ℚ q)
        ( x -ℝ real-ℚ d)
        ( y)
        ( le-real-is-in-lower-cut-ℚ
          ( q)
          ( x -ℝ real-ℚ d)
          ( transpose-add-is-in-lower-cut-ℝ x q d q+d<x))
        ( swap-right-diff-leq-ℝ x y (real-ℚ d) x-y≤d))

  neighborhood-dist-bound-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    leq-ℝ (dist-ℝ x y) (real-ℚ (rational-ℚ⁺ d)) →
    is-in-neighborhood-leq-ℝ l d x y
  neighborhood-dist-bound-ℝ d⁺@(d , _) x y |x-y|≤d =
    ( lower-neighborhood-leq-diff-bound-ℝ
      ( d⁺)
      ( y)
      ( x)
      ( tr
        ( λ z → leq-ℝ z (real-ℚ d))
        ( distributive-neg-diff-ℝ _ _)
        ( transitive-leq-ℝ
          ( neg-ℝ (x -ℝ y))
          ( abs-ℝ (x -ℝ y))
          ( real-ℚ d)
          ( |x-y|≤d)
          ( neg-leq-abs-ℝ _))) ,
      lower-neighborhood-leq-diff-bound-ℝ
      ( d⁺)
      ( x)
      ( y)
      ( transitive-leq-ℝ
        ( x -ℝ y)
        ( abs-ℝ (x -ℝ y))
        ( real-ℚ d)
        ( |x-y|≤d)
        ( leq-abs-ℝ _)))
```

### Triangle inequality

```agda
abstract
  triangle-inequality-dist-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (dist-ℝ x z) (dist-ℝ x y +ℝ dist-ℝ y z)
  triangle-inequality-dist-ℝ x y z =
    preserves-leq-left-sim-ℝ
      ( dist-ℝ x y +ℝ dist-ℝ y z)
      ( abs-ℝ (x -ℝ y +ℝ y -ℝ z))
      ( abs-ℝ (x -ℝ z))
      ( preserves-sim-abs-ℝ
        ( similarity-reasoning-ℝ
          x -ℝ y +ℝ y -ℝ z
          ~ℝ (x -ℝ y +ℝ y) -ℝ z by sim-eq-ℝ (inv (associative-add-ℝ _ _ _))
          ~ℝ x -ℝ z by
            preserves-sim-right-add-ℝ
              ( neg-ℝ z)
              ( x -ℝ y +ℝ y)
              ( x)
              ( cancel-right-diff-add-ℝ x y)))
      ( triangle-inequality-abs-ℝ (x -ℝ y) (y -ℝ z))
```
