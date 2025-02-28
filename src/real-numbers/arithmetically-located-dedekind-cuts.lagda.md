# Arithmetically located Dedekind cuts

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.arithmetically-located-dedekind-cuts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Definition

A pair of a [lower Dedekind cut](real-numbers.lower-dedekind-real-numbers.md)
`L` and an [upper Dedekind cut](real-numbers.upper-dedekind-real-numbers.md) `U`
is
{{#concept "arithmetically located" Disambiguation="Dedekind cut" Agda=arithmetically-located-lower-upper-ℝ}}
if for any [positive](elementary-number-theory.positive-rational-numbers.md)
[rational number](elementary-number-theory.rational-numbers.md) `ε : ℚ⁺`, there
exists `p, q : ℚ` where `p ∈ L` and `q ∈ U`, such that `0 < q - p < ε`.
Intuitively, when `L` and `U` are the lower and upper cuts of a real number `x`,
then `p` and `q` are rational approximations of `x` to within `ε`.

This follows parts of Section 11 in {{#cite BauerTaylor2009}}.

## Definitions

### The predicate of being arithmetically located on pairs of lower and upper Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  arithmetically-located-lower-upper-ℝ : UU (l1 ⊔ l2)
  arithmetically-located-lower-upper-ℝ =
    (ε⁺ : ℚ⁺) →
    exists
      ( ℚ × ℚ)
      ( λ (p , q) → le-ℚ-Prop q (p +ℚ rational-ℚ⁺ ε⁺) ∧
        cut-lower-ℝ x p ∧
        cut-upper-ℝ y q)
```

## Properties

### Arithmetically located cuts are located

If a pair of lower and upper Dedekind cuts is arithmetically located, it is also
located.

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  abstract
    is-located-is-arithmetically-located-lower-upper-ℝ :
      arithmetically-located-lower-upper-ℝ x y →
      is-located-lower-upper-ℝ x y
    is-located-is-arithmetically-located-lower-upper-ℝ
      arithmetically-located p q p<q =
      elim-exists
        ( cut-lower-ℝ x p ∨ cut-upper-ℝ y q)
        ( λ (p' , q') (q'<p'+q-p , p'∈L , q'∈U) →
          rec-coproduct
            ( λ p<p' →
              inl-disjunction
                ( is-in-cut-le-ℚ-lower-ℝ x p p' p<p' p'∈L))
            ( λ p'≤p →
              inr-disjunction
                ( is-in-cut-le-ℚ-upper-ℝ
                  ( y)
                  ( q')
                  ( q)
                  ( concatenate-le-leq-ℚ
                    ( q')
                    ( p' +ℚ (q -ℚ p))
                    ( q)
                    ( q'<p'+q-p)
                  ( tr
                    ( leq-ℚ (p' +ℚ (q -ℚ p)))
                    ( is-identity-right-conjugation-Ab abelian-group-add-ℚ p q)
                    ( preserves-leq-left-add-ℚ (q -ℚ p) p' p p'≤p)))
                  ( q'∈U)))
            ( decide-le-leq-ℚ p p'))
        ( arithmetically-located (positive-diff-le-ℚ p q p<q))
```

## References

{{#bibliography}}
