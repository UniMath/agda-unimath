# Opposite ring extensions of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.opposite-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-integers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.opposite-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

A [ring](ring-theory.rings.md) is an
[extension of ℚ](ring-theory.ring-extensions-rational-numbers.md) if and only if
its [opposite ring](ring-theory.opposite-rings.md) is.

## Definitions

### A ring is an extension of `ℚ` if and only if its opposite ring is

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-op-is-rational-extension-Ring :
    is-rational-extension-Ring R → is-rational-extension-Ring (op-Ring R)
  is-rational-extension-op-is-rational-extension-Ring H k k>0 =
    ( inv-positive-integer-Rational-Extension-Ring (R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Extension-Ring
      ( R , H)
      ( k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Extension-Ring
      ( R , H)
      ( k , k>0))

  is-rational-extension-is-rational-extension-op-Ring :
    is-rational-extension-Ring (op-Ring R) → is-rational-extension-Ring R
  is-rational-extension-is-rational-extension-op-Ring H k k>0 =
    ( inv-positive-integer-Rational-Extension-Ring (op-Ring R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Extension-Ring
      ( op-Ring R , H)
      ( k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Extension-Ring
      ( op-Ring R , H)
      ( k , k>0))

module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  op-Rational-Extension-Ring : Rational-Extension-Ring l
  pr1 op-Rational-Extension-Ring =
    op-Ring (ring-Rational-Extension-Ring R)
  pr2 op-Rational-Extension-Ring =
    is-rational-extension-op-is-rational-extension-Ring
      ( ring-Rational-Extension-Ring R)
      ( is-rational-extension-ring-Rational-Extension-Ring R)
```
