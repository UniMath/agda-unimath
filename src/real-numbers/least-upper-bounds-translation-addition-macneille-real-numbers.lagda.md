# Least upper bounds and rational translation on MacNeille real numbers

```agda
module real-numbers.least-upper-bounds-translation-addition-macneille-real-numbers where
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
  {l1 l2 : Level} →
  (q : ℚ) →
  {I : UU l1} →
  (I → macneille-ℝ l2) →
  I → macneille-ℝ l2
translate-family-right-macneille-real-ℚ q y i =
  add-macneille-ℝ
    ( located-macneille-real-ℚ q)
    ( y i)
```

## Properties

```agda
abstract
  preserves-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
    {l1 l2 l3 : Level} →
    (q : ℚ) →
    {I : UU l1} →
    (y : I → macneille-ℝ l2) →
    (z : macneille-ℝ l3) →
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
    {l1 l2 : Level} →
    (q : ℚ) →
    {I : UU l1} →
    (y : I → macneille-ℝ l2) →
    (z : macneille-ℝ l2) →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ q y)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) z) →
    is-upper-bound-family-of-elements-macneille-ℝ y z
  reflects-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
    q y z q+y≤q+z i =
    reflects-leq-right-add-macneille-real-ℚ
      q
      ( y i)
      ( z)
      ( q+y≤q+z i)

abstract
  iff-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
    {l1 l2 : Level} →
    (q : ℚ) →
    {I : UU l1} →
    (y : I → macneille-ℝ l2) →
    (z : macneille-ℝ l2) →
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
  {l1 l2 : Level} →
  {I : UU l1} →
  (I → macneille-ℝ l2) →
  macneille-ℝ l2 →
  UU (l1 ⊔ lsuc l2)
is-least-upper-bound-family-of-elements-at-level-macneille-ℝ {l2 = l2} y x =
  (z : macneille-ℝ l2) →
  is-upper-bound-family-of-elements-macneille-ℝ y z ↔
  leq-macneille-ℝ x z

abstract
  is-least-upper-bound-family-of-elements-at-level-is-least-upper-bound-family-of-elements-macneille-ℝ :
    {l1 l2 : Level} →
    {I : UU l1} →
    (y : I → macneille-ℝ l2) →
    (x : macneille-ℝ l2) →
    is-least-upper-bound-family-of-elements-macneille-ℝ y x →
    is-least-upper-bound-family-of-elements-at-level-macneille-ℝ y x
  is-least-upper-bound-family-of-elements-at-level-is-least-upper-bound-family-of-elements-macneille-ℝ
    y x x-is-lub-y z =
    x-is-lub-y z
```

```agda
module _
  {l1 l2 : Level}
  (q : ℚ)
  {I : UU l1}
  (y : I → macneille-ℝ l2)
  (x : macneille-ℝ l2)
  (x-is-lub-y : is-least-upper-bound-family-of-elements-at-level-macneille-ℝ y x)
  where

  translated-y :
    I → macneille-ℝ l2
  translated-y =
    translate-family-right-macneille-real-ℚ q y

  translated-x :
    macneille-ℝ l2
  translated-x =
    add-macneille-ℝ
      ( located-macneille-real-ℚ q)
      ( x)

  abstract
    is-upper-bound-y-x :
      is-upper-bound-family-of-elements-macneille-ℝ y x
    is-upper-bound-y-x =
      backward-implication
        ( x-is-lub-y x)
        ( refl-leq-macneille-ℝ x)

  abstract
    forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
      (z : macneille-ℝ l2) →
      is-upper-bound-family-of-elements-macneille-ℝ translated-y z →
      leq-macneille-ℝ translated-x z
    forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
      z q+y≤z =
      tr
        ( λ t → leq-macneille-ℝ translated-x t)
        ( right-inverse-right-translate-macneille-real-ℚ q z)
        ( preserves-leq-right-add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( x)
          ( add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) z)
          ( forward-implication
            ( x-is-lub-y (add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) z))
            ( λ i →
              leq-transpose-right-add-macneille-real-ℚ
                q
                ( y i)
                ( z)
                ( q+y≤z i))))

  abstract
    backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ :
      (z : macneille-ℝ l2) →
      leq-macneille-ℝ translated-x z →
      is-upper-bound-family-of-elements-macneille-ℝ translated-y z
    backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
      z q+x≤z i =
      transitive-leq-macneille-ℝ
        ( add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( y i))
        ( add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( x))
        ( z)
        ( q+x≤z)
        ( preserves-leq-right-add-macneille-ℝ
          ( located-macneille-real-ℚ q)
          ( y i)
          ( x)
          ( is-upper-bound-y-x i))

  abstract
    is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ :
      is-least-upper-bound-family-of-elements-at-level-macneille-ℝ
        translated-y
        translated-x
    is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
      z =
      ( forward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
          z ,
        backward-implication-is-least-upper-bound-family-of-elements-right-translate-macneille-real-ℚ
          z)
```
