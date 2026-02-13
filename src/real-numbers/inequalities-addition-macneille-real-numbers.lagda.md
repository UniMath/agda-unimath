# Inequality preservation for addition on MacNeille real numbers

```agda
module real-numbers.inequalities-addition-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.additive-group-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.minkowski-multiplication-commutative-monoids

open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.addition-macneille-real-numbers
open import real-numbers.addition-upper-dedekind-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Lower and upper cuts

```agda
abstract
  preserves-leq-right-add-lower-ℝ :
    {l1 l2 l3 : Level} →
    (x : lower-ℝ l1) (y : lower-ℝ l2) (z : lower-ℝ l3) →
    leq-lower-ℝ x y →
    leq-lower-ℝ (add-lower-ℝ x z) (add-lower-ℝ y z)
  preserves-leq-right-add-lower-ℝ x y z x≤y =
    preserves-leq-left-minkowski-mul-Commutative-Monoid
      commutative-monoid-add-ℚ
      ( cut-lower-ℝ z)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      x≤y

  preserves-leq-left-add-lower-ℝ :
    {l1 l2 l3 : Level} →
    (x : lower-ℝ l1) (y : lower-ℝ l2) (z : lower-ℝ l3) →
    leq-lower-ℝ x y →
    leq-lower-ℝ (add-lower-ℝ z x) (add-lower-ℝ z y)
  preserves-leq-left-add-lower-ℝ x y z x≤y =
    preserves-leq-right-minkowski-mul-Commutative-Monoid
      commutative-monoid-add-ℚ
      ( cut-lower-ℝ z)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      x≤y

  preserves-leq-right-add-upper-ℝ :
    {l1 l2 l3 : Level} →
    (x : upper-ℝ l1) (y : upper-ℝ l2) (z : upper-ℝ l3) →
    leq-upper-ℝ x y →
    leq-upper-ℝ (add-upper-ℝ x z) (add-upper-ℝ y z)
  preserves-leq-right-add-upper-ℝ x y z x≤y =
    preserves-leq-left-minkowski-mul-Commutative-Monoid
      commutative-monoid-add-ℚ
      ( cut-upper-ℝ z)
      ( cut-upper-ℝ y)
      ( cut-upper-ℝ x)
      x≤y

  preserves-leq-left-add-upper-ℝ :
    {l1 l2 l3 : Level} →
    (x : upper-ℝ l1) (y : upper-ℝ l2) (z : upper-ℝ l3) →
    leq-upper-ℝ x y →
    leq-upper-ℝ (add-upper-ℝ z x) (add-upper-ℝ z y)
  preserves-leq-left-add-upper-ℝ x y z x≤y =
    preserves-leq-right-minkowski-mul-Commutative-Monoid
      commutative-monoid-add-ℚ
      ( cut-upper-ℝ z)
      ( cut-upper-ℝ y)
      ( cut-upper-ℝ x)
      x≤y
```

## MacNeille reals

```agda
abstract opaque
  unfolding add-macneille-ℝ

  preserves-leq-right-add-macneille-ℝ :
    {l1 l2 l3 : Level} →
    (z : located-macneille-ℝ l1) →
    (x : macneille-ℝ l2) →
    (y : macneille-ℝ l3) →
    leq-macneille-ℝ x y →
    leq-macneille-ℝ
      ( add-macneille-ℝ z x)
      ( add-macneille-ℝ z y)
  preserves-leq-right-add-macneille-ℝ z x y x≤y =
    ( preserves-leq-left-add-lower-ℝ
        ( lower-real-macneille-ℝ x)
        ( lower-real-macneille-ℝ y)
        ( lower-real-macneille-ℝ (pr1 z))
        ( pr1 x≤y) ,
      preserves-leq-left-add-upper-ℝ
        ( upper-real-macneille-ℝ x)
        ( upper-real-macneille-ℝ y)
        ( upper-real-macneille-ℝ (pr1 z))
        ( pr2 x≤y))

  preserves-leq-left-add-macneille-ℝ :
    {l1 l2 l3 : Level} →
    (x : located-macneille-ℝ l1) →
    (y : located-macneille-ℝ l2) →
    (z : macneille-ℝ l3) →
    leq-macneille-ℝ (pr1 x) (pr1 y) →
    leq-macneille-ℝ
      ( add-macneille-ℝ x z)
      ( add-macneille-ℝ y z)
  preserves-leq-left-add-macneille-ℝ x y z x≤y =
    ( preserves-leq-right-add-lower-ℝ
        ( lower-real-macneille-ℝ (pr1 x))
        ( lower-real-macneille-ℝ (pr1 y))
        ( lower-real-macneille-ℝ z)
        ( pr1 x≤y) ,
      preserves-leq-right-add-upper-ℝ
        ( upper-real-macneille-ℝ (pr1 x))
        ( upper-real-macneille-ℝ (pr1 y))
        ( upper-real-macneille-ℝ z)
        ( pr2 x≤y))
```
