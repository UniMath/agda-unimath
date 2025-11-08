# Strict inequalities about addition and subtraction on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequalities-addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

This file describes lemmas about
[strict inequalities](real-numbers.strict-inequality-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) related to
[addition](real-numbers.addition-real-numbers.md) and
[subtraction](real-numbers.difference-real-numbers.md).

## Lemmas

### Strict inequality on the real numbers is translation invariant

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  opaque
    unfolding add-ℝ le-ℝ

    preserves-le-right-add-ℝ : le-ℝ x y → le-ℝ (x +ℝ z) (y +ℝ z)
    preserves-le-right-add-ℝ x<y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → upper-cut-ℝ (x +ℝ z) r ∧ lower-cut-ℝ (y +ℝ z) r))
      in do
        ( p , x<p , p<y) ← x<y
        ( q , p<q , q<y) ← forward-implication (is-rounded-lower-cut-ℝ y p) p<y
        ( (r , s) , s<r+q-p , r<z , z<s) ←
          is-arithmetically-located-ℝ
            ( z)
            ( positive-diff-le-ℚ p<q)
        let
          p-q+s<r : le-ℚ ((p -ℚ q) +ℚ s) r
          p-q+s<r =
            tr
              ( le-ℚ ((p -ℚ q) +ℚ s))
              ( equational-reasoning
                  (p -ℚ q) +ℚ (r +ℚ (q -ℚ p))
                  ＝ (p -ℚ q) +ℚ (r -ℚ (p -ℚ q))
                    by
                      ap
                        ( λ t → (p -ℚ q) +ℚ (r +ℚ t))
                        ( inv (distributive-neg-diff-ℚ p q))
                  ＝ r by is-identity-right-conjugation-add-ℚ (p -ℚ q) r)
              ( preserves-le-right-add-ℚ (p -ℚ q) s (r +ℚ (q -ℚ p)) s<r+q-p)
        intro-exists
          ( p +ℚ s)
          ( intro-exists (p , s) (x<p , z<s , refl) ,
            intro-exists
              ( q , (p -ℚ q) +ℚ s)
              ( q<y ,
                le-lower-cut-ℝ z p-q+s<r r<z ,
                ( equational-reasoning
                    p +ℚ s
                    ＝ (q +ℚ (p -ℚ q)) +ℚ s
                      by
                        ap
                          ( _+ℚ s)
                          ( inv (is-identity-right-conjugation-add-ℚ q p))
                    ＝ q +ℚ ((p -ℚ q) +ℚ s) by associative-add-ℚ _ _ _)))

    preserves-le-left-add-ℝ : le-ℝ x y → le-ℝ (z +ℝ x) (z +ℝ y)
    preserves-le-left-add-ℝ x<y =
      binary-tr
        ( le-ℝ)
        ( commutative-add-ℝ x z)
        ( commutative-add-ℝ y z)
        ( preserves-le-right-add-ℝ x<y)

abstract
  preserves-le-diff-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    le-ℝ x y → le-ℝ (x -ℝ z) (y -ℝ z)
  preserves-le-diff-ℝ z = preserves-le-right-add-ℝ (neg-ℝ z)

  reverses-le-diff-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    le-ℝ x y → le-ℝ (z -ℝ y) (z -ℝ x)
  reverses-le-diff-ℝ z x y x<y =
    preserves-le-left-add-ℝ z _ _ (neg-le-ℝ x<y)

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    reflects-le-right-add-ℝ : le-ℝ (x +ℝ z) (y +ℝ z) → le-ℝ x y
    reflects-le-right-add-ℝ x+z<y+z =
      preserves-le-sim-ℝ
        ( cancel-right-add-diff-ℝ x z)
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-le-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z<y+z)

    reflects-le-left-add-ℝ : le-ℝ (z +ℝ x) (z +ℝ y) → le-ℝ x y
    reflects-le-left-add-ℝ z+x<z+y =
      reflects-le-right-add-ℝ
        ( binary-tr
          ( le-ℝ)
          ( commutative-add-ℝ z x)
          ( commutative-add-ℝ z y)
          ( z+x<z+y))

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-translate-right-le-ℝ : le-ℝ x y ↔ le-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-translate-right-le-ℝ = preserves-le-right-add-ℝ z x y
  pr2 iff-translate-right-le-ℝ = reflects-le-right-add-ℝ z x y

  iff-translate-left-le-ℝ : le-ℝ x y ↔ le-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-translate-left-le-ℝ = preserves-le-left-add-ℝ z x y
  pr2 iff-translate-left-le-ℝ = reflects-le-left-add-ℝ z x y

abstract
  preserves-le-add-ℝ :
    {l1 l2 l3 l4 : Level} {a : ℝ l1} {b : ℝ l2} {c : ℝ l3} {d : ℝ l4} →
    le-ℝ a b → le-ℝ c d → le-ℝ (a +ℝ c) (b +ℝ d)
  preserves-le-add-ℝ {a = a} {b = b} {c = c} {d = d} a≤b c≤d =
    transitive-le-ℝ
      ( a +ℝ c)
      ( a +ℝ d)
      ( b +ℝ d)
      ( preserves-le-right-add-ℝ d a b a≤b)
      ( preserves-le-left-add-ℝ a c d c≤d)
```

### `x + y < z` if and only if `x < z - y`

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-left-add-ℝ : le-ℝ (x +ℝ y) z → le-ℝ x (z -ℝ y)
    le-transpose-left-add-ℝ x+y<z =
      preserves-le-left-sim-ℝ
        ( z -ℝ y)
        ( (x +ℝ y) -ℝ y)
        ( x)
        ( cancel-right-add-diff-ℝ x y)
        ( preserves-le-right-add-ℝ (neg-ℝ y) (x +ℝ y) z x+y<z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-left-add-ℝ' : le-ℝ (x +ℝ y) z → le-ℝ y (z -ℝ x)
    le-transpose-left-add-ℝ' x+y<z =
      le-transpose-left-add-ℝ y x z
        ( tr (λ w → le-ℝ w z) (commutative-add-ℝ _ _) x+y<z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-diff-ℝ : le-ℝ x (y -ℝ z) → le-ℝ (x +ℝ z) y
    le-transpose-right-diff-ℝ x<y-z =
      preserves-le-right-sim-ℝ
        ( x +ℝ z)
        ( (y -ℝ z) +ℝ z)
        ( y)
        ( cancel-right-diff-add-ℝ y z)
        ( preserves-le-right-add-ℝ z x (y -ℝ z) x<y-z)

    le-transpose-right-diff-ℝ' : le-ℝ x (y -ℝ z) → le-ℝ (z +ℝ x) y
    le-transpose-right-diff-ℝ' x<y-z =
      tr
        ( λ w → le-ℝ w y)
        ( commutative-add-ℝ _ _)
        ( le-transpose-right-diff-ℝ x<y-z)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  iff-diff-right-le-ℝ : le-ℝ (x +ℝ y) z ↔ le-ℝ x (z -ℝ y)
  iff-diff-right-le-ℝ =
    (le-transpose-left-add-ℝ x y z , le-transpose-right-diff-ℝ x z y)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    iff-add-right-le-ℝ : le-ℝ (x -ℝ y) z ↔ le-ℝ x (z +ℝ y)
    iff-add-right-le-ℝ =
      tr
        ( λ w → le-ℝ (x -ℝ y) z ↔ le-ℝ x (z +ℝ w))
        ( neg-neg-ℝ y)
        ( iff-diff-right-le-ℝ x (neg-ℝ y) z)

    le-transpose-left-diff-ℝ : le-ℝ (x -ℝ y) z → le-ℝ x (z +ℝ y)
    le-transpose-left-diff-ℝ = forward-implication iff-add-right-le-ℝ

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-add-ℝ : le-ℝ x (y +ℝ z) → le-ℝ (x -ℝ z) y
    le-transpose-right-add-ℝ = backward-implication (iff-add-right-le-ℝ x z y)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    le-transpose-right-add-ℝ' : le-ℝ x (y +ℝ z) → le-ℝ (x -ℝ y) z
    le-transpose-right-add-ℝ' x<y+z =
      le-transpose-right-add-ℝ x z y (tr (le-ℝ x) (commutative-add-ℝ _ _) x<y+z)
```

### If `x < y`, then there is some `ε : ℚ⁺` with `x + ε < y`

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} (x<y : le-ℝ x y)
  where

  abstract
    exists-positive-rational-separation-le-ℝ :
      exists ℚ⁺ (λ q → le-prop-ℝ (x +ℝ real-ℚ⁺ q) y)
    exists-positive-rational-separation-le-ℝ =
      let open do-syntax-trunc-Prop (∃ ℚ⁺ (λ q → le-prop-ℝ (x +ℝ real-ℚ⁺ q) y))
      in do
        (q , 0<q , q<y-x) ←
          dense-rational-le-ℝ zero-ℝ (y -ℝ x)
            ( preserves-le-left-sim-ℝ
              ( y -ℝ x)
              ( x -ℝ x)
              ( zero-ℝ)
              ( right-inverse-law-add-ℝ x)
              ( preserves-le-right-add-ℝ (neg-ℝ x) x y x<y))
        intro-exists
          ( q , is-positive-le-zero-ℚ (reflects-le-real-ℚ 0<q))
          ( le-transpose-right-diff-ℝ' _ _ _ q<y-x)
```

### If `x + y < p` for some rational `p`, then there exist `q r : ℚ` such that `p = q + r`, `x < q`, `y < r`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) (p : ℚ)
  where

  abstract opaque
    unfolding add-ℝ

    le-split-add-rational-ℝ :
      le-ℝ (x +ℝ y) (real-ℚ p) →
      exists
        ( ℚ × ℚ)
        ( λ (q , r) →
          Id-Prop ℚ-Set p (q +ℚ r) ∧
          le-prop-ℝ x (real-ℚ q) ∧
          le-prop-ℝ y (real-ℚ r))
    le-split-add-rational-ℝ x+y<p =
      let open do-syntax-trunc-Prop (∃ _ _)
      in do
        ((q , r) , x<q , y<r , p=q+r) ← is-in-upper-cut-le-real-ℚ (x +ℝ y) x+y<p
        intro-exists
          ( q , r)
          ( p=q+r ,
            le-real-is-in-upper-cut-ℚ x x<q ,
            le-real-is-in-upper-cut-ℚ y y<r)
```
