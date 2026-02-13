# Escaping images by greatest postfixpoints of MacNeille-real endomaps

```agda
module real-numbers.not-in-image-greatest-postfixpoints-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.universe-levels

open import real-numbers.greatest-postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
```

</details>

## Idea

Suppose `x0` is a greatest postfixpoint of an endomap `g : ℝₘ → ℝₘ`. If every
index `n` with `f n ＝ x0` yields a strictly greater postfixpoint of `g`, then
`x0` is not in the image of `f`.

## Definition

```agda
has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (g : macneille-ℝ l → macneille-ℝ l) →
  (x0 : macneille-ℝ l) → UU (lsuc l)
has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ f g x0 =
  (n : ℕ) →
  f n ＝ x0 →
  Σ _
    ( λ y →
      le-macneille-ℝ x0 y ×
      is-postfixpoint-endomap-macneille-ℝ g y)

has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (g : macneille-ℝ l → macneille-ℝ l) →
  (x0 : macneille-ℝ l) → UU (lsuc l)
has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ f g x0 =
  (n : ℕ) →
  f n ＝ x0 →
  Σ _
    ( λ y →
      leq-macneille-ℝ x0 y ×
      ¬ (leq-macneille-ℝ y x0) ×
      is-postfixpoint-endomap-macneille-ℝ g y)

abstract
  has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ-has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (g : macneille-ℝ l → macneille-ℝ l) →
    (x0 : macneille-ℝ l) →
    has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
      f g x0 →
    has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
      f g x0
  has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ-has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
    f g x0 strict-step n p =
    ( pr1 (strict-step n p) ,
      leq-le-macneille-ℝ (pr1 (pr2 (strict-step n p))) ,
      not-leq-le-macneille-ℝ
        ( x0)
        ( pr1 (strict-step n p))
        ( pr1 (pr2 (strict-step n p))) ,
      pr2 (pr2 (strict-step n p)))
```

## Theorem

```agda
abstract
  not-in-image-map-ℕ-is-greatest-postfixpoint-not-leq-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (g : macneille-ℝ l → macneille-ℝ l) →
    (x0 : macneille-ℝ l) →
    is-greatest-postfixpoint-endomap-macneille-ℝ g x0 →
    has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
      f g x0 →
    (n : ℕ) → f n ≠ x0
  not-in-image-map-ℕ-is-greatest-postfixpoint-not-leq-macneille-ℝ
    f g x0 is-greatest-postfixpoint-x0 not-leq-step n p =
    pr1 (pr2 (pr2 (not-leq-step n p)))
      ( leq-is-postfixpoint-is-greatest-postfixpoint-endomap-macneille-ℝ
        g x0 is-greatest-postfixpoint-x0
        ( pr1 (not-leq-step n p))
        ( pr2 (pr2 (pr2 (not-leq-step n p)))))

  not-in-image-map-ℕ-is-greatest-postfixpoint-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (g : macneille-ℝ l → macneille-ℝ l) →
    (x0 : macneille-ℝ l) →
    is-greatest-postfixpoint-endomap-macneille-ℝ g x0 →
    has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
      f g x0 →
    (n : ℕ) → f n ≠ x0
  not-in-image-map-ℕ-is-greatest-postfixpoint-macneille-ℝ
    f g x0 is-greatest-postfixpoint-x0 strict-step =
    not-in-image-map-ℕ-is-greatest-postfixpoint-not-leq-macneille-ℝ
      f g x0 is-greatest-postfixpoint-x0
      ( has-not-leq-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ-has-strictly-greater-postfixpoint-at-image-map-ℕ-endomap-macneille-ℝ
        f g x0 strict-step)
```
