# Multiplication of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import foundation.conjunction
open import foundation.logical-equivalences
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.subtypes

open import real-numbers.dedekind-real-numbers
```

</details>

## Definition

```agda

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ q =
    ∃
      ( type-subtype (rational-bounds-ℝ x))
      ( λ ((a , b) , _) →
        ∃
          ( type-subtype (rational-bounds-ℝ y))
          ( λ ((c , d) , _) →
            le-ℚ-Prop
              ( q)
              ( min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))))

  upper-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ q =
    ∃
      ( type-subtype (rational-bounds-ℝ x))
      ( λ ((a , b) , _) →
        ∃
          ( type-subtype (rational-bounds-ℝ y))
          ( λ ((c , d) , _) →
            le-ℚ-Prop
              ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)))
              ( q)))

  abstract
    is-inhabited-lower-cut-mul-ℝ : exists ℚ lower-cut-mul-ℝ
    is-inhabited-lower-cut-mul-ℝ =
      do
        abx@((a , b) , a<x , x<b) ← is-inhabited-rational-bounds-ℝ x
        cdy@((c , d) , c<y , y<d) ← is-inhabited-rational-bounds-ℝ y
        let
          min-ac-ad = min-ℚ (a *ℚ c) (a *ℚ d)
          min-bc-bd = min-ℚ (b *ℚ c) (b *ℚ d)
          min = min-ℚ min-ac-ad min-bc-bd
        (q , q<min) ← exists-lesser-ℚ min
        intro-exists q (intro-exists abx (intro-exists cdy q<min))
      where open do-syntax-trunc-Prop (∃ ℚ lower-cut-mul-ℝ)

    is-inhabited-upper-cut-mul-ℝ : exists ℚ upper-cut-mul-ℝ
    is-inhabited-upper-cut-mul-ℝ =
      do
        abx@((a , b) , a<x , x<b) ← is-inhabited-rational-bounds-ℝ x
        cdy@((c , d) , c<y , y<d) ← is-inhabited-rational-bounds-ℝ y
        let
          max-ac-ad = max-ℚ (a *ℚ c) (a *ℚ d)
          max-bc-bd = max-ℚ (b *ℚ c) (b *ℚ d)
          max = max-ℚ max-ac-ad max-bc-bd
        (q , max<q) ← exists-greater-ℚ max
        intro-exists q (intro-exists abx (intro-exists cdy max<q))
      where open do-syntax-trunc-Prop (∃ ℚ upper-cut-mul-ℝ)

    forward-implication-is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-mul-ℝ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r)
    forward-implication-is-rounded-lower-cut-mul-ℝ q q<mul =
      do
        (abx@((a , b) , a<x , x<b) , q<mul') ← q<mul
        (cdy@((c , d) , c<y , y<d) , q<min) ← q<mul'
        let min = min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
        intro-exists
          ( mediant-ℚ q min)
          ( le-left-mediant-ℚ q min q<min ,
            intro-exists
              ( abx)
              ( intro-exists cdy (le-right-mediant-ℚ q min q<min)))
      where
        open
          do-syntax-trunc-Prop (∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r))

    backward-implication-is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r) →
      is-in-subtype lower-cut-mul-ℝ q
    backward-implication-is-rounded-lower-cut-mul-ℝ q ∃r =
      do
        (r , q<r , r<mul) ← ∃r
        (abx@((a , b) , a<x , x<b) , r<mul') ← r<mul
        (cdy@((c , d) , c<y , y<d) , r<min) ← r<mul'
        let min = min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
        intro-exists abx (intro-exists cdy (transitive-le-ℚ q r min r<min q<r))
      where open do-syntax-trunc-Prop (lower-cut-mul-ℝ q)

    is-rounded-lower-cut-mul-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-mul-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-mul-ℝ r)
    is-rounded-lower-cut-mul-ℝ q =
      forward-implication-is-rounded-lower-cut-mul-ℝ q ,
      backward-implication-is-rounded-lower-cut-mul-ℝ q

    forward-implication-is-rounded-upper-cut-mul-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-mul-ℝ q →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p)
    forward-implication-is-rounded-upper-cut-mul-ℝ q mul<q =
      do
        (abx@((a , b) , a<x , x<b) , mul'<q) ← mul<q
        (cdy@((c , d) , c<y , y<d) , max<q) ← mul'<q
        let max = max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d))
        intro-exists
          ( mediant-ℚ max q)
          ( le-right-mediant-ℚ max q max<q ,
            intro-exists abx (intro-exists cdy (le-left-mediant-ℚ max q max<q)))
      where
        open
          do-syntax-trunc-Prop (∃ ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p))

    backward-implication-is-rounded-upper-cut-mul-ℝ :
      (q : ℚ) →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p) →
      is-in-subtype upper-cut-mul-ℝ q
    backward-implication-is-rounded-upper-cut-mul-ℝ q ∃p =
      do
        (p , p<q , mul<p) ← ∃p
        (abx@((a , b) , a<x , x<b) , mul'<p) ← mul<p
        (cdy@((c , d) , c<y , y<d) , max<p) ← mul'<p
        let max = max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d))
        intro-exists abx (intro-exists cdy (transitive-le-ℚ max p q p<q max<p))
      where open do-syntax-trunc-Prop (upper-cut-mul-ℝ q)

    is-rounded-upper-cut-mul-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-mul-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-mul-ℝ p)
    is-rounded-upper-cut-mul-ℝ q =
      forward-implication-is-rounded-upper-cut-mul-ℝ q ,
      backward-implication-is-rounded-upper-cut-mul-ℝ q
```
