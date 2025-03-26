# Multiplication of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.inequality-real-numbers
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

    is-disjoint-lower-upper-cut-mul-ℝ :
      disjoint-subtype lower-cut-mul-ℝ upper-cut-mul-ℝ
    is-disjoint-lower-upper-cut-mul-ℝ q (q<mul , mul<q) =
      do
        (abx@((a , b) , a<x , x<b) , q<mul') ← q<mul
        (cdy@((c , d) , c<y , y<d) , q<min) ← q<mul'
        (abx'@((a' , b') , a'<x , x<b') , mul<q') ← mul<q
        (cdy'@((c' , d') , c'<y , y<c') , max<q) ← mul<q'
        let
          min = min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
          max =
            max-ℚ (max-ℚ (a' *ℚ c') (a' *ℚ d')) (max-ℚ (b' *ℚ c') (b' *ℚ d'))
          leq-lower-upper-x p q p<x x<q =
            leq-le-ℚ {p} {q} (le-lower-upper-cut-ℝ x p q p<x x<q)
          leq-lower-upper-y p q p<y y<q =
            leq-le-ℚ {p} {q} (le-lower-upper-cut-ℝ y p q p<y y<q)
        irreflexive-le-ℚ
          ( q)
          ( transitive-le-ℚ
            ( q)
            ( max)
            ( q)
            ( max<q)
            ( concatenate-le-leq-ℚ
              ( q)
              ( min)
              ( max)
              ( q<min)
              ( leq-lower-upper-bounds-mul-closed-interval-ℚ
                ( a)
                ( b)
                ( c)
                ( d)
                ( a')
                ( b')
                ( c')
                ( d')
                ( leq-lower-upper-x a b a<x x<b)
                ( leq-lower-upper-y c d c<y y<d)
                ( leq-lower-upper-x a' b' a'<x x<b')
                ( leq-lower-upper-y c' d' c'<y y<c')
                ( leq-lower-upper-x a b' a<x x<b')
                ( leq-lower-upper-x a' b a'<x x<b)
                ( leq-lower-upper-y c d' c<y y<c')
                ( leq-lower-upper-y c' d c'<y y<d))))
      where open do-syntax-trunc-Prop empty-Prop

  lower-real-mul-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-mul-ℝ =
    lower-cut-mul-ℝ ,
    is-inhabited-lower-cut-mul-ℝ ,
    is-rounded-lower-cut-mul-ℝ

  upper-real-mul-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-mul-ℝ =
    upper-cut-mul-ℝ ,
    is-inhabited-upper-cut-mul-ℝ ,
    is-rounded-upper-cut-mul-ℝ

  abstract
    is-arithmetically-located-lower-upper-mul-ℝ :
      is-arithmetically-located-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ
    is-arithmetically-located-lower-upper-mul-ℝ ε⁺@(ε , _) =
      do
        p , |x|<p ← is-inhabited-upper-cut-ℝ (abs-ℝ x)
        q , |y|<q ← is-inhabited-upper-cut-ℝ (abs-ℝ y)
        let
          p⁺ : ℚ⁺
          p⁺ = p , is-positive-upper-cut-abs-ℝ p x |x|<p
          q⁺ : ℚ⁺
          q⁺ = q , is-positive-upper-cut-abs-ℝ q y |y|<q
          (ε₁⁺@(ε₁ , _) , ε₂⁺@(ε₂ , _) , ε₁+ε₂=ε) = split-ℚ⁺ ε⁺
          (δ⁺@(δ , _) , δ<1 , δ<ε₁/⟨q+1⟩) =
            strict-min-law-ℚ⁺ one-ℚ⁺ (ε₁⁺ *ℚ⁺ inv-ℚ⁺ (q⁺ +ℚ⁺ one-ℚ⁺))
          (θ⁺@(θ , _) , θ<1 , θ<ε₂/⟨p+1⟩) =
            strict-min-law-ℚ⁺ one-ℚ⁺ (ε₂⁺ *ℚ⁺ inv-ℚ⁺ (p⁺ +ℚ⁺ one-ℚ⁺))
        ((a , b) , b<a+δ , a<x , x<b) ← is-arithmetically-located-ℝ x δ⁺
        ((c , d) , d<c+θ , c<y , y<d) ← is-arithmetically-located-ℝ y θ⁺
        {!   !}
      where
        open
          do-syntax-trunc-Prop
            (∃
              ( ℚ × ℚ)
              ( λ (p , q) → le-ℚ-Prop q (p +ℚ rational-ℚ⁺ ε⁺) ∧
                cut-lower-ℝ lower-real-mul-ℝ p ∧
                cut-upper-ℝ upper-real-mul-ℝ q))
```
