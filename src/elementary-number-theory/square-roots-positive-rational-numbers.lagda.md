# Square roots of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.square-roots-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications

open import order-theory.posets
```

</details>

## Idea

This file expresses bounds and properties of bounds on
{{#concept "square roots" Disambiguation="of positive rational numbers"}} of
[positive](elementary-number-theory.positive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md).

## Properties

### For any positive rational number `q`, there is a positive rational number `p` with `p² < q`

```agda
module _
  (q : ℚ⁺)
  where

  abstract
    bound-square-le-ℚ⁺ : Σ ℚ⁺ (λ p → le-ℚ⁺ (p *ℚ⁺ p) q)
    bound-square-le-ℚ⁺ =
      trichotomy-le-ℚ (rational-ℚ⁺ q) one-ℚ
        ( λ q<1 → (q , le-left-mul-less-than-one-ℚ⁺ q q<1 q))
        ( λ q=1 →
          let
            p = mediant-zero-ℚ⁺ one-ℚ⁺
            p<1 = le-mediant-zero-ℚ⁺ one-ℚ⁺
          in
            ( p ,
              inv-tr
                ( le-ℚ⁺ (p *ℚ⁺ p))
                ( eq-ℚ⁺ q=1)
                ( transitive-le-ℚ _ _ _
                  ( p<1)
                  ( le-right-mul-less-than-one-ℚ⁺ p p<1 p))))
        ( λ 1<q →
          ( one-ℚ⁺ ,
            inv-tr (λ p → le-ℚ⁺ p q) (left-unit-law-mul-ℚ⁺ one-ℚ⁺) 1<q))

    square-le-ℚ⁺ : exists ℚ⁺ (λ p → le-prop-ℚ⁺ (p *ℚ⁺ p) q)
    square-le-ℚ⁺ = unit-trunc-Prop bound-square-le-ℚ⁺
```

### For any positive rational number `q`, there is a positive rational number `p` with `q < p²`

```agda
module _
  (q : ℚ⁺)
  where

  abstract
    bound-square-le-ℚ⁺' : Σ ℚ⁺ (λ p → le-ℚ⁺ q (p *ℚ⁺ p))
    bound-square-le-ℚ⁺' =
      trichotomy-le-ℚ (rational-ℚ⁺ q) one-ℚ
        ( λ q<1 →
          ( one-ℚ⁺ , inv-tr (le-ℚ⁺ q) (right-unit-law-mul-ℚ⁺ one-ℚ⁺) q<1))
        ( λ q=1 →
          ( positive-rational-ℕ⁺ (2 , λ ()) ,
            binary-tr
              ( le-ℚ)
              ( inv q=1)
              ( inv (mul-rational-ℕ 2 2))
              ( preserves-le-rational-ℕ 1 4 _)))
        ( λ 1<q →
          ( q , le-left-mul-greater-than-one-ℚ⁺ q 1<q q))

    square-le-ℚ⁺' : exists ℚ⁺ (λ p → le-prop-ℚ⁺ q (p *ℚ⁺ p))
    square-le-ℚ⁺' = unit-trunc-Prop bound-square-le-ℚ⁺'
```

### For any positive rational numbers `p` and `q`, if `p² < q`, then there is an `r` with `p < r` and `r² < q`

```agda
abstract
  bound-rounded-below-square-le-ℚ⁺ :
    (p q : ℚ⁺) → le-ℚ⁺ (p *ℚ⁺ p) q →
    Σ ℚ⁺ (λ r → le-ℚ⁺ p r × le-ℚ⁺ (r *ℚ⁺ r) q)
  bound-rounded-below-square-le-ℚ⁺ p⁺@(p , _) q⁺@(q , _) p²<q =
    let
      (δ₁⁺@(δ₁ , _) , δ₁+δ₁<⟨q-p²⟩/p) =
        bound-double-le-ℚ⁺ (positive-diff-le-ℚ (p *ℚ p) q p²<q *ℚ⁺ inv-ℚ⁺ p⁺)
      (δ₂⁺@(δ₂ , _) , δ₂+δ₂<δ₁) = bound-double-le-ℚ⁺ δ₁⁺
      δ₃⁺@(δ₃ , _) = min-ℚ⁺ δ₂⁺ p⁺
      δ₂<δ₁ : le-ℚ δ₂ δ₁
      δ₂<δ₁ =
        transitive-le-ℚ δ₂ (δ₂ +ℚ δ₂) δ₁
          ( δ₂+δ₂<δ₁)
          ( le-right-add-rational-ℚ⁺ δ₂ δ₂⁺)
      δ₃≤δ₂ : leq-ℚ δ₃ δ₂
      δ₃≤δ₂ = leq-left-min-ℚ⁺ _ _
      open inequality-reasoning-Poset ℚ-Poset
    in
      ( p⁺ +ℚ⁺ δ₃⁺ ,
        le-right-add-rational-ℚ⁺ p δ₃⁺ ,
        concatenate-leq-le-ℚ
          ( (p +ℚ δ₃) *ℚ (p +ℚ δ₃))
          ( p *ℚ p +ℚ (δ₁ +ℚ δ₁) *ℚ p)
          ( q)
          ( chain-of-inequalities
            (p +ℚ δ₃) *ℚ (p +ℚ δ₃)
            ≤ (p +ℚ δ₃) *ℚ p +ℚ (p +ℚ δ₃) *ℚ δ₃
              by leq-eq-ℚ _ _ (left-distributive-mul-add-ℚ (p +ℚ δ₃) p δ₃)
            ≤ (p +ℚ δ₃) *ℚ p +ℚ ((p *ℚ δ₃) +ℚ (δ₃ *ℚ δ₃))
              by leq-eq-ℚ _ _
                ( ap-add-ℚ refl (right-distributive-mul-add-ℚ _ _ _))
            ≤ (p +ℚ δ₃) *ℚ p +ℚ ((δ₃ *ℚ p) +ℚ (δ₃ *ℚ p))
              by
                preserves-leq-right-add-ℚ _ _ _
                  ( preserves-leq-add-ℚ
                    ( leq-eq-ℚ _ _ (commutative-mul-ℚ _ _))
                    ( preserves-leq-left-mul-ℚ⁺
                      ( δ₃⁺)
                      ( δ₃)
                      ( p)
                      ( leq-right-min-ℚ⁺ _ _)))
            ≤ (p +ℚ (δ₃ +ℚ δ₃ +ℚ δ₃)) *ℚ p
              by leq-eq-ℚ _ _
                ( equational-reasoning
                  (p +ℚ δ₃) *ℚ p +ℚ (δ₃ *ℚ p +ℚ δ₃ *ℚ p)
                  ＝ (p +ℚ δ₃) *ℚ p +ℚ (δ₃ +ℚ δ₃) *ℚ p
                    by ap-add-ℚ refl (inv (right-distributive-mul-add-ℚ _ _ _))
                  ＝ ((p +ℚ δ₃) +ℚ (δ₃ +ℚ δ₃)) *ℚ p
                    by inv (right-distributive-mul-add-ℚ _ _ _)
                  ＝ (p +ℚ (δ₃ +ℚ (δ₃ +ℚ δ₃))) *ℚ p
                    by ap-mul-ℚ (associative-add-ℚ _ _ _) refl
                  ＝ (p +ℚ (δ₃ +ℚ δ₃ +ℚ δ₃)) *ℚ p
                    by
                      ap-mul-ℚ
                        ( ap-add-ℚ refl (inv (associative-add-ℚ _ _ _)))
                        ( refl))
            ≤ (p +ℚ (δ₂ +ℚ δ₂ +ℚ δ₂)) *ℚ p
              by
                preserves-leq-right-mul-ℚ⁺ p⁺ _ _
                  ( preserves-leq-right-add-ℚ p _ _
                    ( preserves-leq-add-ℚ
                      ( preserves-leq-add-ℚ δ₃≤δ₂ δ₃≤δ₂)
                      ( δ₃≤δ₂)))
            ≤ (p +ℚ (δ₁ +ℚ δ₁)) *ℚ p
              by
                preserves-leq-right-mul-ℚ⁺ p⁺ _ _
                  ( preserves-leq-right-add-ℚ p _ _
                    ( preserves-leq-add-ℚ
                      ( leq-le-ℚ δ₂+δ₂<δ₁)
                      ( leq-le-ℚ δ₂<δ₁)))
            ≤ p *ℚ p +ℚ (δ₁ +ℚ δ₁) *ℚ p
              by leq-eq-ℚ _ _ (right-distributive-mul-add-ℚ _ _ _))
          ( tr
            ( le-ℚ (p *ℚ p +ℚ (δ₁ +ℚ δ₁) *ℚ p))
            ( equational-reasoning
              p *ℚ p +ℚ
              ((q -ℚ p *ℚ p) *ℚ rational-inv-ℚ⁺ p⁺) *ℚ p
              ＝ p *ℚ p +ℚ (q -ℚ p *ℚ p)
                by
                  ap-add-ℚ
                    ( refl)
                    ( ap
                      ( rational-ℚ⁺)
                      ( is-section-right-mul-ℚ⁺
                        ( p⁺)
                        ( positive-diff-le-ℚ _ _ p²<q)))
              ＝ q
                by is-identity-right-conjugation-add-ℚ (p *ℚ p) q)
            ( preserves-le-right-add-ℚ (p *ℚ p) _ _
              ( preserves-le-right-mul-ℚ⁺ p⁺ _ _ δ₁+δ₁<⟨q-p²⟩/p))))

  rounded-below-square-le-ℚ⁺ :
    (p q : ℚ⁺) → le-ℚ⁺ (p *ℚ⁺ p) q →
    exists ℚ⁺ (λ r → le-prop-ℚ⁺ p r ∧ le-prop-ℚ⁺ (r *ℚ⁺ r) q)
  rounded-below-square-le-ℚ⁺ p q p²<q =
    unit-trunc-Prop (bound-rounded-below-square-le-ℚ⁺ p q p²<q)
```

### For any positive rational numbers `p` and `q`, if `q < p²`, then there is an `r` with `r < p` and `q < r²`

```agda
abstract
  bound-rounded-above-square-le-ℚ⁺ :
    (p q : ℚ⁺) → le-ℚ⁺ q (p *ℚ⁺ p) →
    Σ ℚ⁺ (λ r → le-ℚ⁺ r p × le-ℚ⁺ q (r *ℚ⁺ r))
  bound-rounded-above-square-le-ℚ⁺ p⁺@(p , _) q⁺@(q , _) q<p² =
    let
      (δ⁺@(δ , _) , δ+δ<⟨p²-q⟩/p) =
        bound-double-le-ℚ⁺ ( positive-diff-le-ℚ _ _ q<p² *ℚ⁺ inv-ℚ⁺ p⁺)
      δ<p =
        transitive-le-ℚ δ (δ +ℚ δ) p
          ( transitive-le-ℚ
            ( δ +ℚ δ)
            ( (p *ℚ p -ℚ q) *ℚ rational-inv-ℚ⁺ p⁺)
            ( p)
            ( tr
              ( le-ℚ _)
              ( ap rational-ℚ⁺ (is-retraction-right-mul-ℚ⁺ p⁺ p⁺))
              ( preserves-le-right-mul-ℚ⁺ (inv-ℚ⁺ p⁺) _ _
                ( le-diff-rational-ℚ⁺ (p *ℚ p) q⁺)))
            ( δ+δ<⟨p²-q⟩/p))
          ( le-right-add-rational-ℚ⁺ δ δ⁺)
    in
      ( positive-diff-le-ℚ _ _ δ<p ,
        le-diff-rational-ℚ⁺ p δ⁺ ,
        transitive-le-ℚ
          ( q)
          ( p *ℚ p -ℚ (δ +ℚ δ) *ℚ p)
          ( square-ℚ (p -ℚ δ))
          ( inv-tr
            ( le-ℚ _)
            ( equational-reasoning
              square-ℚ (p -ℚ δ)
              ＝ square-ℚ p -ℚ rational-ℕ 2 *ℚ (p *ℚ δ) +ℚ square-ℚ δ
                by square-diff-ℚ p δ
              ＝ square-ℚ p -ℚ p *ℚ (rational-ℕ 2 *ℚ δ) +ℚ square-ℚ δ
                by ap-add-ℚ (ap-diff-ℚ refl (left-swap-mul-ℚ _ _ _)) refl
              ＝ square-ℚ p -ℚ p *ℚ (δ +ℚ δ) +ℚ square-ℚ δ
                by ap-add-ℚ (ap-diff-ℚ refl (ap-mul-ℚ refl (mul-two-ℚ δ))) refl
              ＝ square-ℚ p -ℚ (δ +ℚ δ) *ℚ p +ℚ square-ℚ δ
                by ap-add-ℚ (ap-diff-ℚ refl (commutative-mul-ℚ _ _)) refl)
            ( le-right-add-rational-ℚ⁺ _ (δ⁺ *ℚ⁺ δ⁺)))
          ( binary-tr
            ( le-ℚ)
            ( ( ap-add-ℚ refl (distributive-neg-diff-ℚ _ _)) ∙
              ( is-identity-right-conjugation-add-ℚ (p *ℚ p) q))
            ( refl)
            ( preserves-le-right-add-ℚ (p *ℚ p) _ _
              ( neg-le-ℚ _ _
                ( tr
                  ( le-ℚ _)
                  ( ap
                    ( rational-ℚ⁺)
                    ( is-section-right-mul-ℚ⁺ p⁺ (positive-diff-le-ℚ _ _ q<p²)))
                  ( preserves-le-right-mul-ℚ⁺ p⁺ _ _ δ+δ<⟨p²-q⟩/p))))))

  rounded-above-square-le-ℚ⁺ :
    (p q : ℚ⁺) → le-ℚ⁺ q (p *ℚ⁺ p) →
    exists ℚ⁺ (λ r → le-prop-ℚ⁺ r p ∧ le-prop-ℚ⁺ q (r *ℚ⁺ r))
  rounded-above-square-le-ℚ⁺ p q p²<q =
    unit-trunc-Prop (bound-rounded-above-square-le-ℚ⁺ p q p²<q)
```
