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

A pair of a [lower Dedekind real](real-numbers.lower-dedekind-real-numbers.md)
`L` and an [upper Dedekind real](real-numbers.upper-dedekind-real-numbers.md)
`U` is {{#concept "arithmetically located" Disambiguation="Dedekind cut"}} if
for any positive [rational number](elementary-number-theory.rational-numbers.md)
`ε : ℚ`, there exists `p, q : ℚ` where `p ∈ L` and `q ∈ U`, such that
`0 < q - p < ε`. Intuitively, when `L , U` represent the cuts of a real number
`x`, `p` and `q` are rational approximations of `x` to within `ε`. This follows
parts of Section 11 in {{#cite BauerTaylor2009}}.

## Definitions

### The predicate of being arithmetically located on pairs of subtypes of rational numbers

```agda
module _
  {l : Level} (L : lower-ℝ l) (U : upper-ℝ l)
  where

  arithmetically-located-lower-upper-ℝ : UU l
  arithmetically-located-lower-upper-ℝ =
    (ε⁺ : ℚ⁺) →
    exists
      ( ℚ × ℚ)
      ( λ (p , q) → le-ℚ-Prop q (p +ℚ rational-ℚ⁺ ε⁺) ∧
        cut-lower-ℝ L p ∧
        cut-upper-ℝ U q)
```

## Properties

### Arithmetically located cuts are located

If a cut is arithmetically located and closed under strict inequality on the
rational numbers, it is also located.

```agda
module _
  {l : Level} (x : lower-ℝ l) (y : upper-ℝ l)
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
