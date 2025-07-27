# The distance between real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.distance-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "distance function" Disambiguation="between real numbers" Agda=dist-ℝ}}
on two [real numbers](real-numbers.dedekind-real-numbers.md) measures how far
they are apart. It is the
[absolute value](real-numbers.absolute-value-real-numbers.md) of their
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

### Distances are nonnegative

```agda
abstract
  is-nonnegative-dist-ℝ :
    {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → is-nonnegative-ℝ (dist-ℝ x y)
  is-nonnegative-dist-ℝ _ _ = is-nonnegative-abs-ℝ _
```

### Relationship to the metric space of real numbers

Two real numbers `x` and `y` are in an `ε`-neighborhood of each other if and
only if their distance is at most `ε`.

```agda
abstract
  diff-bound-neighborhood-leq-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y →
    x -ℝ y ≤-ℝ real-ℚ (rational-ℚ⁺ d)
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
    y -ℝ x ≤-ℝ real-ℚ (rational-ℚ⁺ d)
  reversed-diff-bound-neighborhood-leq-ℝ d x y H =
    diff-bound-neighborhood-leq-ℝ d y x (is-symmetric-premetric-leq-ℝ d x y H)

  leq-dist-neighborhood-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y →
    dist-ℝ x y ≤-ℝ real-ℚ (rational-ℚ⁺ d)
  leq-dist-neighborhood-ℝ d⁺@(d , _) x y H =
    leq-abs-leq-leq-neg-ℝ
      ( x -ℝ y)
      ( real-ℚ d)
      ( diff-bound-neighborhood-leq-ℝ d⁺ x y H)
      ( inv-tr
        ( λ z → leq-ℝ z (real-ℚ d))
        ( distributive-neg-diff-ℝ _ _)
        ( reversed-diff-bound-neighborhood-leq-ℝ d⁺ x y H))

  lower-neighborhood-leq-diff-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    x -ℝ y ≤-ℝ real-ℚ (rational-ℚ⁺ d) →
    is-in-lower-neighborhood-leq-ℝ d y x
  lower-neighborhood-leq-diff-ℝ d⁺@(d , _) x y x-y≤d q q+d<x =
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

  neighborhood-leq-dist-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    dist-ℝ x y ≤-ℝ real-ℚ (rational-ℚ⁺ d) →
    is-in-neighborhood-leq-ℝ l d x y
  neighborhood-leq-dist-ℝ d⁺@(d , _) x y |x-y|≤d =
    ( lower-neighborhood-leq-diff-ℝ
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
      lower-neighborhood-leq-diff-ℝ
      ( d⁺)
      ( x)
      ( y)
      ( transitive-leq-ℝ
        ( x -ℝ y)
        ( abs-ℝ (x -ℝ y))
        ( real-ℚ d)
        ( |x-y|≤d)
        ( leq-abs-ℝ _)))

  neighborhood-iff-leq-dist-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    is-in-neighborhood-leq-ℝ l d x y ↔
    dist-ℝ x y ≤-ℝ real-ℚ (rational-ℚ⁺ d)
  neighborhood-iff-leq-dist-ℝ d x y =
    ( leq-dist-neighborhood-ℝ d x y ,
      neighborhood-leq-dist-ℝ d x y)
```

### Triangle inequality

```agda
abstract
  triangle-inequality-dist-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    dist-ℝ x z ≤-ℝ dist-ℝ x y +ℝ dist-ℝ y z
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

### Bounds on both differences of real numbers are bounds on their distance

```agda
abstract
  leq-dist-leq-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    x -ℝ y ≤-ℝ z →
    y -ℝ x ≤-ℝ z →
    dist-ℝ x y ≤-ℝ z
  leq-dist-leq-diff-ℝ x y z x-y≤z y-x≤z =
    leq-abs-leq-leq-neg-ℝ
      ( _)
      ( z)
      ( x-y≤z)
      ( inv-tr (λ w → leq-ℝ w z) (distributive-neg-diff-ℝ _ _) y-x≤z)
```

### Addition preserves distance between real numbers

```agda
abstract
  preserves-dist-left-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ
      ( dist-ℝ (add-ℝ x y) (add-ℝ x z))
      ( dist-ℝ y z)
  preserves-dist-left-add-ℝ x y z =
    similarity-reasoning-ℝ
      dist-ℝ (x +ℝ y) (x +ℝ z)
      ~ℝ abs-ℝ ((x -ℝ x) +ℝ (y -ℝ z))
        by sim-eq-ℝ (ap abs-ℝ (interchange-law-diff-add-ℝ x y x z))
      ~ℝ abs-ℝ (zero-ℝ +ℝ y -ℝ z)
        by
          preserves-sim-abs-ℝ
            ( preserves-sim-right-add-ℝ
              ( y -ℝ z)
              ( x -ℝ x)
              ( zero-ℝ)
              ( right-inverse-law-add-ℝ x))
      ~ℝ dist-ℝ y z
        by sim-eq-ℝ (ap abs-ℝ (left-unit-law-add-ℝ (y -ℝ z)))

  preserves-dist-right-add-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    sim-ℝ
      ( dist-ℝ (add-ℝ x z) (add-ℝ y z))
      ( dist-ℝ x y)
  preserves-dist-right-add-ℝ z x y =
    similarity-reasoning-ℝ
      dist-ℝ (x +ℝ z) (y +ℝ z)
      ~ℝ abs-ℝ ((x -ℝ y) +ℝ (z -ℝ z))
        by sim-eq-ℝ (ap abs-ℝ (interchange-law-diff-add-ℝ x z y z))
      ~ℝ abs-ℝ (x -ℝ y +ℝ zero-ℝ)
        by
          preserves-sim-abs-ℝ
            ( preserves-sim-left-add-ℝ
              ( x -ℝ y)
              ( z -ℝ z)
              ( zero-ℝ)
              ( right-inverse-law-add-ℝ z))
      ~ℝ dist-ℝ x y
        by sim-eq-ℝ (ap abs-ℝ (right-unit-law-add-ℝ (x -ℝ y)))
```
