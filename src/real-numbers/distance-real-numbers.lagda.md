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

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metrics-of-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
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

ap-dist-ℝ :
  {l1 l2 : Level} {x x' : ℝ l1} → x ＝ x' → {y y' : ℝ l2} → y ＝ y' →
  dist-ℝ x y ＝ dist-ℝ x' y'
ap-dist-ℝ = ap-binary dist-ℝ
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

nonnegative-dist-ℝ :
  {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → ℝ⁰⁺ (l1 ⊔ l2)
nonnegative-dist-ℝ x y = (dist-ℝ x y , is-nonnegative-dist-ℝ x y)
```

### Relationship to the metric space of real numbers

Two real numbers `x` and `y` are in an `ε`-neighborhood of each other in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
[if and only if](foundation.logical-equivalences.md) their distance is
[at most](real-numbers.inequality-real-numbers.md) `ε`.

```agda
abstract opaque
  unfolding leq-ℝ neighborhood-ℝ

  diff-bound-neighborhood-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    neighborhood-ℝ l d x y →
    x -ℝ y ≤-ℝ real-ℚ⁺ d
  diff-bound-neighborhood-ℝ d⁺@(d , _) x y (H , K) =
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

abstract
  reversed-diff-bound-neighborhood-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    neighborhood-ℝ l d x y →
    y -ℝ x ≤-ℝ real-ℚ⁺ d
  reversed-diff-bound-neighborhood-ℝ d x y H =
    diff-bound-neighborhood-ℝ d y x (is-symmetric-neighborhood-ℝ d x y H)

  leq-dist-neighborhood-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    neighborhood-ℝ l d x y →
    dist-ℝ x y ≤-ℝ real-ℚ⁺ d
  leq-dist-neighborhood-ℝ d⁺@(d , _) x y H =
    leq-abs-leq-leq-neg-ℝ
      ( diff-bound-neighborhood-ℝ d⁺ x y H)
      ( inv-tr
        ( λ z → leq-ℝ z (real-ℚ d))
        ( distributive-neg-diff-ℝ _ _)
        ( reversed-diff-bound-neighborhood-ℝ d⁺ x y H))

  lower-neighborhood-diff-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    x -ℝ y ≤-ℝ real-ℚ⁺ d →
    lower-neighborhood-ℝ d y x
  lower-neighborhood-diff-ℝ d⁺@(d , _) x y x-y≤d q q+d<x =
    is-in-lower-cut-le-real-ℚ
      ( y)
      ( concatenate-le-leq-ℝ
        ( real-ℚ q)
        ( x -ℝ real-ℚ d)
        ( y)
        ( le-real-is-in-lower-cut-ℚ
          ( x -ℝ real-ℚ d)
          ( transpose-add-is-in-lower-cut-ℝ x q d q+d<x))
        ( swap-right-diff-leq-ℝ x y (real-ℚ d) x-y≤d))

abstract opaque
  unfolding neighborhood-ℝ

  neighborhood-dist-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    dist-ℝ x y ≤-ℝ real-ℚ⁺ d →
    neighborhood-ℝ l d x y
  neighborhood-dist-ℝ d⁺@(d , _) x y |x-y|≤d =
    ( lower-neighborhood-diff-ℝ
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
      lower-neighborhood-diff-ℝ
      ( d⁺)
      ( x)
      ( y)
      ( transitive-leq-ℝ
        ( x -ℝ y)
        ( abs-ℝ (x -ℝ y))
        ( real-ℚ d)
        ( |x-y|≤d)
        ( leq-abs-ℝ _)))

abstract
  neighborhood-iff-leq-dist-ℝ :
    {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
    neighborhood-ℝ l d x y ↔
    dist-ℝ x y ≤-ℝ real-ℚ⁺ d
  neighborhood-iff-leq-dist-ℝ d x y =
    ( leq-dist-neighborhood-ℝ d x y ,
      neighborhood-dist-ℝ d x y)
```

### The distance function on two real numbers is a metric on the metric space of real numbers

```agda
abstract
  dist-is-metric-of-metric-space-ℝ :
    (l : Level) →
    is-metric-of-Metric-Space
      ( metric-space-ℝ l)
      ( nonnegative-dist-ℝ)
  dist-is-metric-of-metric-space-ℝ _ = neighborhood-iff-leq-dist-ℝ
```

### Triangle inequality

```agda
abstract
  triangle-inequality-dist-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    dist-ℝ x z ≤-ℝ dist-ℝ x y +ℝ dist-ℝ y z
  triangle-inequality-dist-ℝ x y z =
    preserves-leq-left-sim-ℝ
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
      ( x-y≤z)
      ( inv-tr (λ w → leq-ℝ w z) (distributive-neg-diff-ℝ _ _) y-x≤z)

  leq-dist-leq-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    x ≤-ℝ z +ℝ y →
    y ≤-ℝ z +ℝ x →
    dist-ℝ x y ≤-ℝ z
  leq-dist-leq-add-ℝ x y z x≤z+y y≤z+x =
    leq-dist-leq-diff-ℝ x y z
      ( leq-transpose-right-add-ℝ _ _ _ x≤z+y)
      ( leq-transpose-right-add-ℝ _ _ _ y≤z+x)
```

### Addition preserves distance between real numbers

```agda
abstract
  preserves-dist-left-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ
      ( dist-ℝ (x +ℝ y) (x +ℝ z))
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
      ( dist-ℝ (x +ℝ z) (y +ℝ z))
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

### Distributivity laws

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    left-distributive-abs-mul-dist-ℝ :
      abs-ℝ x *ℝ dist-ℝ y z ＝ dist-ℝ (x *ℝ y) (x *ℝ z)
    left-distributive-abs-mul-dist-ℝ =
      equational-reasoning
        abs-ℝ x *ℝ abs-ℝ (y -ℝ z)
        ＝ abs-ℝ (x *ℝ (y -ℝ z))
          by inv (abs-mul-ℝ x (y -ℝ z))
        ＝ dist-ℝ (x *ℝ y) (x *ℝ z)
          by ap abs-ℝ (left-distributive-mul-diff-ℝ x y z)

    right-distributive-abs-mul-dist-ℝ :
      dist-ℝ x y *ℝ abs-ℝ z ＝ dist-ℝ (x *ℝ z) (y *ℝ z)
    right-distributive-abs-mul-dist-ℝ =
      equational-reasoning
        abs-ℝ (x -ℝ y) *ℝ abs-ℝ z
        ＝ abs-ℝ ((x -ℝ y) *ℝ z)
          by inv (abs-mul-ℝ (x -ℝ y) z)
        ＝ dist-ℝ (x *ℝ z) (y *ℝ z)
          by ap abs-ℝ (right-distributive-mul-diff-ℝ x y z)
```

### Zero laws

```agda
abstract
  right-zero-law-dist-ℝ : {l : Level} (x : ℝ l) → dist-ℝ x zero-ℝ ＝ abs-ℝ x
  right-zero-law-dist-ℝ x = ap abs-ℝ (right-unit-law-diff-ℝ x)

  left-zero-law-dist-ℝ : {l : Level} (x : ℝ l) → dist-ℝ zero-ℝ x ＝ abs-ℝ x
  left-zero-law-dist-ℝ x = commutative-dist-ℝ zero-ℝ x ∙ right-zero-law-dist-ℝ x
```

### Distance is preserved by similarity

```agda
abstract
  preserves-dist-left-sim-ℝ :
    {l1 l2 l3 : Level} {z : ℝ l1} {x : ℝ l2} {y : ℝ l3} → sim-ℝ x y →
    sim-ℝ (dist-ℝ x z) (dist-ℝ y z)
  preserves-dist-left-sim-ℝ {z = z} {x = x} {y = y} x~y =
    preserves-sim-abs-ℝ (preserves-sim-right-add-ℝ (neg-ℝ z) x y x~y)

  preserves-dist-right-sim-ℝ :
    {l1 l2 l3 : Level} {z : ℝ l1} {x : ℝ l2} {y : ℝ l3} → sim-ℝ x y →
    sim-ℝ (dist-ℝ z x) (dist-ℝ z y)
  preserves-dist-right-sim-ℝ {z = z} x~y =
    preserves-sim-abs-ℝ (preserves-sim-diff-ℝ (refl-sim-ℝ z) x~y)

  preserves-dist-sim-ℝ :
    {l1 l2 l3 l4 : Level} {x : ℝ l1} {x' : ℝ l2} {y : ℝ l3} {y' : ℝ l4} →
    sim-ℝ x x' → sim-ℝ y y' → sim-ℝ (dist-ℝ x y) (dist-ℝ x' y')
  preserves-dist-sim-ℝ x~x' y~y' =
    transitive-sim-ℝ _ _ _
      ( preserves-dist-right-sim-ℝ y~y')
      ( preserves-dist-left-sim-ℝ x~x')
```

### The distance from a real number to itself is 0

```agda
abstract
  diagonal-dist-ℝ : {l : Level} (x : ℝ l) → sim-ℝ (dist-ℝ x x) zero-ℝ
  diagonal-dist-ℝ x =
    similarity-reasoning-ℝ
      dist-ℝ x x
      ~ℝ abs-ℝ zero-ℝ
        by preserves-sim-abs-ℝ (right-inverse-law-add-ℝ x)
      ~ℝ zero-ℝ
        by sim-eq-ℝ abs-zero-ℝ
```
