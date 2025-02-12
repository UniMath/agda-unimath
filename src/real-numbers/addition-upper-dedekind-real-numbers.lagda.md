# Addition of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-upper-dedekind-real-numbers where
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

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.minkowski-multiplication-commutative-monoids

open import logic.functoriality-existential-quantification

open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The sum of two
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md) is
the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
their cuts.

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  cut-add-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-add-upper-ℝ =
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)

  is-in-cut-add-upper-ℝ : ℚ → UU (l1 ⊔ l2)
  is-in-cut-add-upper-ℝ = is-in-subtype cut-add-upper-ℝ

  is-inhabited-cut-add-upper-ℝ : exists ℚ cut-add-upper-ℝ
  is-inhabited-cut-add-upper-ℝ =
    minkowski-mul-inhabited-is-inhabited-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)
      ( is-inhabited-cut-upper-ℝ x)
      ( is-inhabited-cut-upper-ℝ y)

  abstract
    is-rounded-cut-add-upper-ℝ :
      (q : ℚ) →
      is-in-cut-add-upper-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-add-upper-ℝ p)
    pr1 (is-rounded-cut-add-upper-ℝ q) =
      elim-exists
        ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ cut-add-upper-ℝ p))
        ( λ (ux , uy) (x<ux , y<uy , q=ux+uy) →
          map-binary-exists
            ( λ p → le-ℚ p q × is-in-cut-add-upper-ℝ p)
            ( add-ℚ)
            ( λ ux' uy' (ux'<ux , x<ux') (uy'<uy , y<uy') →
              tr
                ( le-ℚ (ux' +ℚ uy'))
                ( inv (q=ux+uy))
                ( preserves-le-add-ℚ {ux'} {ux} {uy'} {uy} ux'<ux uy'<uy) ,
              intro-exists (ux' , uy') (x<ux' , y<uy' , refl))
            ( forward-implication (is-rounded-cut-upper-ℝ x ux) x<ux)
            ( forward-implication (is-rounded-cut-upper-ℝ y uy) y<uy))
    pr2 (is-rounded-cut-add-upper-ℝ q) =
      elim-exists
        ( cut-add-upper-ℝ q)
        ( λ p (p<q , x+y<r) →
          elim-exists
            ( cut-add-upper-ℝ q)
            ( λ (px , py) (x<px , y<py , p=px+py) →
              let
                q-p⁺ = positive-diff-le-ℚ p q p<q
                ε⁺ = mediant-zero-ℚ⁺ q-p⁺
                ε = rational-ℚ⁺ ε⁺
                ε<q-p = le-mediant-zero-ℚ⁺ q-p⁺
              in
                intro-exists
                  ( px +ℚ ε , q -ℚ (px +ℚ ε))
                  ( is-in-cut-le-ℚ-upper-ℝ
                    ( x)
                    ( px)
                    ( px +ℚ ε)
                    ( le-right-add-rational-ℚ⁺ px ε⁺)
                    ( x<px) ,
                    is-in-cut-le-ℚ-upper-ℝ
                      ( y)
                      ( py)
                      ( q -ℚ (px +ℚ ε))
                      ( binary-tr
                        ( le-ℚ)
                        ( equational-reasoning
                            (q -ℚ px) -ℚ (q -ℚ p)
                            ＝ neg-ℚ (q -ℚ p) +ℚ (q -ℚ px)
                              by commutative-add-ℚ (q -ℚ px) (neg-ℚ (q -ℚ p))
                            ＝ (p -ℚ q) +ℚ (q -ℚ px)
                              by
                                ap (_+ℚ (q -ℚ px)) (distributive-neg-diff-ℚ q p)
                            ＝ p -ℚ px by triangle-diff-ℚ p q px
                            ＝ (px +ℚ py) -ℚ px by ap (_-ℚ px) p=px+py
                            ＝ py
                              by
                                is-identity-left-conjugation-Ab
                                  ( abelian-group-add-ℚ)
                                  ( px)
                                  ( py))
                        ( equational-reasoning
                          (q -ℚ px) -ℚ ε
                          ＝ q +ℚ (neg-ℚ px +ℚ neg-ℚ ε)
                            by associative-add-ℚ q (neg-ℚ px) (neg-ℚ ε)
                          ＝ q -ℚ (px +ℚ ε)
                            by ap (q +ℚ_) (inv (distributive-neg-add-ℚ px ε)))
                        ( preserves-le-right-add-ℚ
                          ( q -ℚ px)
                          ( neg-ℚ (q -ℚ p))
                          ( neg-ℚ ε)
                          ( neg-le-ℚ ε (q -ℚ p) ε<q-p)))
                      ( y<py) ,
                    inv
                      ( is-identity-right-conjugation-Ab
                        ( abelian-group-add-ℚ)
                        ( px +ℚ ε)
                        ( q))))
            ( x+y<r))

  add-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  pr1 add-upper-ℝ = cut-add-upper-ℝ
  pr1 (pr2 add-upper-ℝ) = is-inhabited-cut-add-upper-ℝ
  pr2 (pr2 add-upper-ℝ) = is-rounded-cut-add-upper-ℝ
```

## Properties

### Addition of upper Dedekind real numbers is commutative

```agda
module _
  {l1 l2 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2)
  where

  commutative-add-upper-ℝ : add-upper-ℝ x y ＝ add-upper-ℝ y x
  commutative-add-upper-ℝ =
    eq-eq-cut-upper-ℝ
      ( add-upper-ℝ x y)
      ( add-upper-ℝ y x)
      ( commutative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-upper-ℝ x)
        ( cut-upper-ℝ y))
```

### Addition of upper Dedekind real numbers is associative

```agda
module _
  {l1 l2 l3 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2) (z : upper-ℝ l3)
  where

  associative-add-upper-ℝ :
    add-upper-ℝ (add-upper-ℝ x y) z ＝ add-upper-ℝ x (add-upper-ℝ y z)
  associative-add-upper-ℝ =
    eq-eq-cut-upper-ℝ
      ( add-upper-ℝ (add-upper-ℝ x y) z)
      ( add-upper-ℝ x (add-upper-ℝ y z))
      ( associative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-upper-ℝ x)
        ( cut-upper-ℝ y)
        ( cut-upper-ℝ z))
```
