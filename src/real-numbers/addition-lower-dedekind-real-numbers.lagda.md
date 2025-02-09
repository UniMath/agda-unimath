# Addition of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-lower-dedekind-real-numbers where
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
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.minkowski-multiplication-commutative-monoids

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The sum of two [lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md)
is the Minkowski sum of their cuts.

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-add-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-add-lower-ℝ =
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)

  is-in-cut-add-lower-ℝ : ℚ → UU (l1 ⊔ l2)
  is-in-cut-add-lower-ℝ = is-in-subtype cut-add-lower-ℝ

  is-inhabited-add-lower-ℝ : exists ℚ cut-add-lower-ℝ
  is-inhabited-add-lower-ℝ =
    minkowski-mul-inhabited-is-inhabited-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      ( is-inhabited-cut-lower-ℝ x)
      ( is-inhabited-cut-lower-ℝ y)

  abstract
    is-rounded-cut-add-lower-ℝ :
      (q : ℚ) →
      is-in-cut-add-lower-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-add-lower-ℝ r)
    pr1 (is-rounded-cut-add-lower-ℝ q) =
      elim-exists
        ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ cut-add-lower-ℝ r))
        ( λ (lx , ly) (lx<x , ly<y , q=lx+ly) →
          map-binary-exists
            ( λ r → le-ℚ q r × is-in-cut-add-lower-ℝ r)
            ( add-ℚ)
            ( λ lx' ly' (lx<lx' , lx'<x) (ly<ly' , ly'<y) →
              tr
                ( λ p → le-ℚ p (lx' +ℚ ly'))
                ( inv q=lx+ly)
                ( preserves-le-add-ℚ {lx} {lx'} {ly} {ly'} lx<lx' ly<ly') ,
              intro-exists (lx' , ly') (lx'<x , ly'<y , refl))
            ( forward-implication (is-rounded-cut-lower-ℝ x lx) lx<x)
            ( forward-implication (is-rounded-cut-lower-ℝ y ly) ly<y))
    pr2 (is-rounded-cut-add-lower-ℝ q) =
      elim-exists
        ( cut-add-lower-ℝ q)
        ( λ r (q<r , r<x+y) →
          elim-exists
            ( cut-add-lower-ℝ q)
            ( λ (rx , ry) (rx<x , ry<y , r=rx+ry) →
              let
                r-q⁺ : ℚ⁺
                r-q⁺ = positive-diff-le-ℚ q r q<r
                ε⁺ : ℚ⁺
                ε⁺ = mediant-zero-ℚ⁺ r-q⁺
                ε : ℚ
                ε = rational-ℚ⁺ ε⁺
                ε<r-q : le-ℚ ε (r -ℚ q)
                ε<r-q = le-mediant-zero-ℚ⁺ r-q⁺
              in
              intro-exists
                ( rx -ℚ ε , q -ℚ (rx -ℚ ε))
                ( le-cut-lower-ℝ
                    ( x)
                    ( rx -ℚ ε)
                    ( rx)
                    ( le-diff-rational-ℚ⁺ rx ε⁺)
                    ( rx<x) ,
                  le-cut-lower-ℝ
                    ( y)
                    ( q -ℚ (rx -ℚ ε))
                    ( ry)
                    ( binary-tr
                        ( le-ℚ)
                        ( equational-reasoning
                          (q -ℚ rx) +ℚ ε
                          ＝ q +ℚ (neg-ℚ rx +ℚ ε)
                            by associative-add-ℚ q (neg-ℚ rx) ε
                          ＝ q +ℚ (ε -ℚ rx)
                            by ap (q +ℚ_) (commutative-add-ℚ (neg-ℚ rx) ε)
                          ＝ q -ℚ (rx -ℚ ε)
                            by ap (q +ℚ_) (inv (distributive-neg-diff-ℚ rx ε)))
                        ( equational-reasoning
                          (q -ℚ rx) +ℚ (r -ℚ q)
                          ＝ (q -ℚ rx) +ℚ (neg-ℚ q +ℚ r)
                            by
                              ap ((q -ℚ rx) +ℚ_) (commutative-add-ℚ r (neg-ℚ q))
                          ＝ (q -ℚ q) +ℚ (neg-ℚ rx +ℚ r)
                            by
                              interchange-law-add-add-ℚ q (neg-ℚ rx) (neg-ℚ q) r
                          ＝ zero-ℚ +ℚ (neg-ℚ rx +ℚ r)
                            by
                              ap
                                ( _+ℚ (neg-ℚ rx +ℚ r))
                                ( right-inverse-law-add-ℚ q)
                          ＝ neg-ℚ rx +ℚ r by left-unit-law-add-ℚ (neg-ℚ rx +ℚ r)
                          ＝ neg-ℚ rx +ℚ (rx +ℚ ry) by ap (neg-ℚ rx +ℚ_) r=rx+ry
                          ＝ ry
                            by is-retraction-left-div-Group group-add-ℚ rx ry)
                        ( preserves-le-right-add-ℚ
                          ( q -ℚ rx)
                          ( ε)
                          ( r -ℚ q)
                          ( ε<r-q)))
                    ( ry<y) ,
                  inv
                    ( is-identity-right-conjugation-Ab
                      ( abelian-group-add-ℚ)
                      ( rx -ℚ ε)
                      ( q))))
            ( r<x+y))

    add-lower-ℝ : lower-ℝ (l1 ⊔ l2)
    pr1 add-lower-ℝ = cut-add-lower-ℝ
    pr1 (pr2 add-lower-ℝ) = is-inhabited-add-lower-ℝ
    pr2 (pr2 add-lower-ℝ) = is-rounded-cut-add-lower-ℝ
```

## Properties

### Addition of lower Dedekind real numbers is commutative

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : lower-ℝ l2)
  where

--   commutative-add-lower-ℝ :
```
