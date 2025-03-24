# The Archimedean property of integer fractions

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.archimedean-property-integer-fractions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-integers funext univalence truncations
open import elementary-number-theory.integer-fractions funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions funext univalence truncations
open import elementary-number-theory.multiplication-integers funext univalence truncations
open import elementary-number-theory.multiplication-positive-and-negative-integers funext univalence truncations
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-integer-fractions funext univalence truncations
open import elementary-number-theory.strict-inequality-integer-fractions funext univalence truncations
open import elementary-number-theory.strict-inequality-integers funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.existential-quantification funext univalence truncations
open import foundation.identity-types funext
open import foundation.propositional-truncations funext univalence
open import foundation.transport-along-identifications
```

</details>

## Definition

The Archimedean property of the integer fractions is that for any
`x y : fraction-ℤ`, with positive `x`, there is an `n : ℕ` such that `y` is less
than `n` as an integer fraction times `x`.

```agda
abstract
  bound-archimedean-property-fraction-ℤ :
    (x y : fraction-ℤ) →
    is-positive-fraction-ℤ x →
    Σ ℕ (λ n → le-fraction-ℤ y (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
  bound-archimedean-property-fraction-ℤ
    x@(px , qx , pos-qx) y@(py , qy , pos-qy) pos-px =
      let
        (n , H) =
          bound-archimedean-property-ℤ
            ( px *ℤ qy)
            ( py *ℤ qx)
            ( is-positive-mul-ℤ pos-px pos-qy)
      in
        n ,
        tr
          ( le-ℤ (py *ℤ qx))
          ( inv (associative-mul-ℤ (int-ℕ n) px qy))
          ( H)

  archimedean-property-fraction-ℤ :
    (x y : fraction-ℤ) →
    is-positive-fraction-ℤ x →
    exists
      ℕ
      (λ n → le-fraction-ℤ-Prop y (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x))
  archimedean-property-fraction-ℤ x y pos-x =
    unit-trunc-Prop (bound-archimedean-property-fraction-ℤ x y pos-x)
```
