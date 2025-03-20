# The Archimedean property of the positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

open import foundation.function-extensionality-axiom

module
  elementary-number-theory.archimedean-property-positive-rational-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-rational-numbers funext
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers funext
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers funext
open import elementary-number-theory.positive-rational-numbers funext
open import elementary-number-theory.rational-numbers funext
open import elementary-number-theory.strict-inequality-rational-numbers funext

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification funext
open import foundation.identity-types funext
open import foundation.propositional-truncations funext
open import foundation.transport-along-identifications
```

</details>

## Definition

The
{{#concept "Archimedean property" Disambiguation="positive rational numbers" Agda=archimedean-property-ℚ⁺}}
of `ℚ⁺` is that for any two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`x y : ℚ⁺`, there is a
[nonzero natural number](elementary-number-theory.nonzero-natural-numbers.md)
`n` such that `y` is
[less than](elementary-number-theory.strict-inequality-rational-numbers.md) `n`
times `x`.

```agda
abstract
  bound-archimedean-property-ℚ⁺ :
    (x y : ℚ⁺) →
    Σ ℕ⁺ (λ n → le-ℚ⁺ y (positive-rational-ℕ⁺ n *ℚ⁺ x))
  bound-archimedean-property-ℚ⁺ (x , pos-x) (y , pos-y) =
    let
      (n , y<nx) = bound-archimedean-property-ℚ x y pos-x
      n≠0 : is-nonzero-ℕ n
      n≠0 n=0 =
        asymmetric-le-ℚ
          ( zero-ℚ)
          ( y)
          ( le-zero-is-positive-ℚ y pos-y)
          ( tr
            ( le-ℚ y)
            ( equational-reasoning
              rational-ℤ (int-ℕ n) *ℚ x
              ＝ rational-ℤ (int-ℕ 0) *ℚ x
                by ap (λ m → rational-ℤ (int-ℕ m) *ℚ x) n=0
              ＝ zero-ℚ by left-zero-law-mul-ℚ x)
            y<nx)
    in (n , n≠0) , y<nx

  archimedean-property-ℚ⁺ :
    (x y : ℚ⁺) →
    exists ℕ⁺ (λ n → le-prop-ℚ⁺ y (positive-rational-ℕ⁺ n *ℚ⁺ x))
  archimedean-property-ℚ⁺ x y =
    unit-trunc-Prop (bound-archimedean-property-ℚ⁺ x y)
```
