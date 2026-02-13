# Least upper bounds and rational translation on MacNeille real numbers

```agda
module real-numbers.least-upper-bounds-rational-translation-addition-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-macneille-real-numbers
open import real-numbers.inequalities-addition-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.least-upper-bounds-families-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.rational-translation-macneille-real-numbers
open import real-numbers.upper-bounds-families-macneille-real-numbers
```

</details>

## Definitions

```agda
translate-family-right-macneille-real-ℚ :
  {l1 l2 : Level} (q : ℚ) {I : UU l1} →
  (I → macneille-ℝ l2) → I → macneille-ℝ l2
translate-family-right-macneille-real-ℚ q y i =
  add-macneille-ℝ (located-macneille-real-ℚ q) (y i)
```

## Properties

```agda
abstract
  preserves-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
    {l1 l2 l3 : Level} (q : ℚ) {I : UU l1}
    (y : I → macneille-ℝ l2) (z : macneille-ℝ l3) →
    is-upper-bound-family-of-elements-macneille-ℝ y z →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ q y)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) z)
  preserves-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
    q y z y≤z i =
    preserves-leq-right-add-macneille-ℝ
      ( located-macneille-real-ℚ q)
      ( y i)
      ( z)
      ( y≤z i)

abstract
  reflects-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
    {l1 l2 : Level} (q : ℚ) {I : UU l1}
    (y : I → macneille-ℝ l2) (z : macneille-ℝ l2) →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ q y)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) z) →
    is-upper-bound-family-of-elements-macneille-ℝ y z
  reflects-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
    q y z q+y≤q+z i =
    reflects-leq-right-add-macneille-real-ℚ q (y i) z (q+y≤q+z i)

abstract
  iff-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
    {l1 l2 : Level} (q : ℚ) {I : UU l1}
    (y : I → macneille-ℝ l2) (z : macneille-ℝ l2) →
    is-upper-bound-family-of-elements-macneille-ℝ y z ↔
    is-upper-bound-family-of-elements-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ q y)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) z)
  iff-upper-bound-family-of-elements-right-translate-macneille-real-ℚ q y z =
    ( preserves-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
        q y z ,
      reflects-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
        q y z)
```

```agda
is-least-upper-bound-family-of-elements-at-level-macneille-ℝ :
  {l1 l2 : Level} {I : UU l1} →
  (I → macneille-ℝ l2) →
  macneille-ℝ l2 →
  UU (l1 ⊔ lsuc l2)
is-least-upper-bound-family-of-elements-at-level-macneille-ℝ {l2 = l2} y x =
  (z : macneille-ℝ l2) →
  is-upper-bound-family-of-elements-macneille-ℝ y z ↔
  leq-macneille-ℝ x z

module _
  {l1 l2 : Level} (q : ℚ) {I : UU l1}
  (y : I → macneille-ℝ l2) (x : macneille-ℝ l2)
  (is-lub-x : is-least-upper-bound-family-of-elements-at-level-macneille-ℝ y x)
  (let q+y = translate-family-right-macneille-real-ℚ q y)
  (let q+x = add-macneille-ℝ (located-macneille-real-ℚ q) x)
  (let ub-x = backward-implication (is-lub-x x) (refl-leq-macneille-ℝ x))
  where

  abstract
    forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
      (z : macneille-ℝ l2) →
      is-upper-bound-family-of-elements-macneille-ℝ q+y z →
      leq-macneille-ℝ q+x z
    forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
      z q+y≤z =
      tr
        ( leq-macneille-ℝ q+x)
        ( right-inverse-right-translate-macneille-real-ℚ q z)
        ( preserves-leq-right-add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( x)
          ( add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) z)
          ( forward-implication
            ( is-lub-x (add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) z))
            ( λ i →
              leq-transpose-right-add-macneille-real-ℚ q (y i) z (q+y≤z i))))

  abstract
    backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
      (z : macneille-ℝ l2) →
      leq-macneille-ℝ q+x z →
      is-upper-bound-family-of-elements-macneille-ℝ q+y z
    backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
      z q+x≤z i =
      transitive-leq-macneille-ℝ
        ( add-macneille-ℝ (located-macneille-real-ℚ q) (y i))
        ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
        ( z)
        ( q+x≤z)
        ( preserves-leq-right-add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( y i)
          ( x)
          ( ub-x i))

  abstract
    is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ :
      is-least-upper-bound-family-of-elements-at-level-macneille-ℝ q+y q+x
    is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
      z =
      ( forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
          z ,
        backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
          z)
```
