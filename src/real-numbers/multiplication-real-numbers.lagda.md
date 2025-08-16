# Multiplication of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.posets

open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

We introduce
{{#concept "multiplication" Disambiguation="real numbers" Agda=mul-ℝ}} on the
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) and derive its
basic properties.

## Definition

```agda
strict-rational-bounds-ℝ : {l : Level} → ℝ l → UU l
strict-rational-bounds-ℝ x =
  type-subtype (lower-cut-ℝ x) × type-subtype (upper-cut-ℝ x)

abstract
  is-inhabited-strict-rational-bounds-ℝ :
    {l : Level} → (x : ℝ l) → is-inhabited (strict-rational-bounds-ℝ x)
  is-inhabited-strict-rational-bounds-ℝ x =
    let
      open do-syntax-trunc-Prop (is-inhabited-Prop (strict-rational-bounds-ℝ x))
    in do
      p ← is-inhabited-lower-cut-ℝ x
      p' ← is-inhabited-upper-cut-ℝ x
      unit-trunc-Prop (p , p')

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ r =
    ∃ ( strict-rational-bounds-ℝ x × strict-rational-bounds-ℝ y)
      ( λ (((p , p<x) , (p' , x<p')) , ((q , q<y) , (q' , y<q'))) →
        le-ℚ-Prop
          ( r)
          ( min-ℚ (min-ℚ (p *ℚ q) (p *ℚ q')) (min-ℚ (p' *ℚ q) (p' *ℚ q'))))

  upper-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  upper-cut-mul-ℝ r =
    ∃ ( strict-rational-bounds-ℝ x × strict-rational-bounds-ℝ y)
      ( λ (((p , p<x) , (p' , x<p')) , ((q , q<y) , (q' , y<q'))) →
        le-ℚ-Prop
          ( max-ℚ (max-ℚ (p *ℚ q) (p *ℚ q')) (max-ℚ (p' *ℚ q) (p' *ℚ q')))
          ( r))

  abstract
    is-inhabited-lower-cut-mul-ℝ : is-inhabited-subtype lower-cut-mul-ℝ
    is-inhabited-lower-cut-mul-ℝ =
      let open do-syntax-trunc-Prop (is-inhabited-subtype-Prop lower-cut-mul-ℝ)
      in do
        bounds-x@((p , _) , (p' , _)) ←
          is-inhabited-strict-rational-bounds-ℝ x
        bounds-y@((q , _) , (q' , _)) ←
          is-inhabited-strict-rational-bounds-ℝ y
        let min = min-ℚ (min-ℚ (p *ℚ q) (p *ℚ q')) (min-ℚ (p' *ℚ q) (p' *ℚ q'))
        (r , r<min) ← exists-lesser-ℚ min
        intro-exists r (intro-exists (bounds-x , bounds-y) r<min)

    is-inhabited-upper-cut-mul-ℝ : is-inhabited-subtype upper-cut-mul-ℝ
    is-inhabited-upper-cut-mul-ℝ =
      let open do-syntax-trunc-Prop (is-inhabited-subtype-Prop upper-cut-mul-ℝ)
      in do
        bounds-x@((p , _) , (p' , _)) ←
          is-inhabited-strict-rational-bounds-ℝ x
        bounds-y@((q , _) , (q' , _)) ←
          is-inhabited-strict-rational-bounds-ℝ y
        let max = max-ℚ (max-ℚ (p *ℚ q) (p *ℚ q')) (max-ℚ (p' *ℚ q) (p' *ℚ q'))
        (r , max<r) ← exists-greater-ℚ max
        intro-exists r (intro-exists (bounds-x , bounds-y) max<r)

    forward-implication-is-rounded-lower-cut-mul-ℝ :
      (a : ℚ) →
      is-in-subtype lower-cut-mul-ℝ a →
      exists ℚ (λ b → le-ℚ-Prop a b ∧ lower-cut-mul-ℝ b)
    forward-implication-is-rounded-lower-cut-mul-ℝ a a∈L =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ b → le-ℚ-Prop a b ∧ lower-cut-mul-ℝ b))
      in do
        ( ( bounds-x@((p , _) , (p' , _)) ,
            bounds-y@((q , _) , (q' , _))) ,
          a<min) ← a∈L
        let min = min-ℚ (min-ℚ (p *ℚ q) (p *ℚ q')) (min-ℚ (p' *ℚ q) (p' *ℚ q'))
        intro-exists
          ( mediant-ℚ a min)
          ( le-left-mediant-ℚ _ _ a<min ,
            intro-exists (bounds-x , bounds-y) (le-right-mediant-ℚ _ _ a<min))

    forward-implication-is-rounded-upper-cut-mul-ℝ :
      (b : ℚ) →
      is-in-subtype upper-cut-mul-ℝ b →
      exists ℚ (λ a → le-ℚ-Prop a b ∧ upper-cut-mul-ℝ a)
    forward-implication-is-rounded-upper-cut-mul-ℝ b b∈U =
      let
        open
          do-syntax-trunc-Prop (∃ ℚ (λ a → le-ℚ-Prop a b ∧ upper-cut-mul-ℝ a))
      in do
        ( ( bounds-x@((p , _) , (p' , _)) ,
            bounds-y@((q , _) , (q' , _))) ,
          max<b) ← b∈U
        let max = max-ℚ (max-ℚ (p *ℚ q) (p *ℚ q')) (max-ℚ (p' *ℚ q) (p' *ℚ q'))
        intro-exists
          ( mediant-ℚ max b)
          ( le-right-mediant-ℚ _ _ max<b ,
            intro-exists (bounds-x , bounds-y) (le-left-mediant-ℚ _ _ max<b))

    backward-implication-is-rounded-lower-cut-mul-ℝ :
      (a : ℚ) →
      exists ℚ (λ b → le-ℚ-Prop a b ∧ lower-cut-mul-ℝ b) →
      is-in-subtype lower-cut-mul-ℝ a
    backward-implication-is-rounded-lower-cut-mul-ℝ a ∃b =
      let open do-syntax-trunc-Prop (lower-cut-mul-ℝ a)
      in do
        ( b , a<b , b∈L) ← ∃b
        ( ( bounds-x@((p , _) , (p' , _)) ,
            bounds-y@((q , _) , (q' , _))) ,
          b<min) ← b∈L
        intro-exists (bounds-x , bounds-y) (transitive-le-ℚ _ b _ b<min a<b)

    backward-implication-is-rounded-upper-cut-mul-ℝ :
      (b : ℚ) →
      exists ℚ (λ a → le-ℚ-Prop a b ∧ upper-cut-mul-ℝ a) →
      is-in-subtype upper-cut-mul-ℝ b
    backward-implication-is-rounded-upper-cut-mul-ℝ b ∃a =
      let open do-syntax-trunc-Prop (upper-cut-mul-ℝ b)
      in do
        ( a , a<b , a∈U) ← ∃a
        ( ( bounds-x@((p , _) , (p' , _)) ,
            bounds-y@((q , _) , (q' , _))) ,
          max<a) ← a∈U
        intro-exists (bounds-x , bounds-y) (transitive-le-ℚ _ a _ a<b max<a)

  lower-real-mul-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-mul-ℝ =
    ( lower-cut-mul-ℝ ,
      is-inhabited-lower-cut-mul-ℝ ,
      λ a →
        ( forward-implication-is-rounded-lower-cut-mul-ℝ a ,
          backward-implication-is-rounded-lower-cut-mul-ℝ a))

  upper-real-mul-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-mul-ℝ =
    ( upper-cut-mul-ℝ ,
      is-inhabited-upper-cut-mul-ℝ ,
      λ a →
        ( forward-implication-is-rounded-upper-cut-mul-ℝ a ,
          backward-implication-is-rounded-upper-cut-mul-ℝ a))

  abstract
    is-disjoint-lower-upper-cut-mul-ℝ :
      disjoint-subtype lower-cut-mul-ℝ upper-cut-mul-ℝ
    is-disjoint-lower-upper-cut-mul-ℝ q (q∈L , q∈U) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        ( (((a , a<x) , (b , x<b)) , ((c , c<y) , (d , y<d))) ,
          q<min-ac-ad-bc-bd) ← q∈L
        ( (((a' , a'<x) , (b' , x<b')) , ((c' , c'<y) , (d' , y<d'))) ,
          max-a'c'-a'd'-b'c'-b'd'<q) ← q∈U
        let
          min-ac-ad-bc-bd =
            min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
          max-a'c'-a'd'-b'c'-b'd' =
            max-ℚ (max-ℚ (a' *ℚ c') (a' *ℚ d')) (max-ℚ (b' *ℚ c') (b' *ℚ d'))
        irreflexive-le-ℚ q
          (transitive-le-ℚ q min-ac-ad-bc-bd q
            ( concatenate-leq-le-ℚ
              ( min-ac-ad-bc-bd)
              ( max-a'c'-a'd'-b'c'-b'd')
              ( q)
              ( transitive-leq-ℚ
                ( min-ac-ad-bc-bd)
                ( max-ℚ a a' *ℚ max-ℚ c c')
                ( max-a'c'-a'd'-b'c'-b'd')
                ( pr2
                  ( mul-closed-interval-closed-interval-ℚ
                    ( a')
                    ( b')
                    ( max-ℚ a a')
                    ( c')
                    ( d')
                    ( max-ℚ c c')
                    ( leq-right-max-ℚ _ _ ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ x a b' a<x x<b')
                        ( leq-lower-upper-cut-ℝ x a' b' a'<x x<b'))
                    ( leq-right-max-ℚ _ _ ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ y c d' c<y y<d')
                        ( leq-lower-upper-cut-ℝ y c' d' c'<y y<d'))))
                ( pr1
                  ( mul-closed-interval-closed-interval-ℚ
                    ( a)
                    ( b)
                    ( max-ℚ a a')
                    ( c)
                    ( d)
                    ( max-ℚ c c')
                    ( leq-left-max-ℚ _ _ ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ x a b a<x x<b)
                        ( leq-lower-upper-cut-ℝ x a' b a'<x x<b))
                    ( leq-left-max-ℚ _ _ ,
                      leq-max-leq-both-ℚ _ _ _
                        ( leq-lower-upper-cut-ℝ y c d c<y y<d)
                        ( leq-lower-upper-cut-ℝ y c' d c'<y y<d)))))
              max-a'c'-a'd'-b'c'-b'd'<q)
            q<min-ac-ad-bc-bd)

    is-arithmetically-located-mul-ℝ :
      is-arithmetically-located-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ
    is-arithmetically-located-mul-ℝ ε =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( close-bounds-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ ε))
      in do
        (Nx , bound-Nx) ← natural-bound-location-ℝ x one-ℚ⁺
        (Ny , bound-Ny) ← natural-bound-location-ℝ y one-ℚ⁺
        let
          N = max-ℕ Nx Ny
          -- To make sure we have values strictly < and > the min and max
          -- whose difference is strictly less than ε, we need to split
          -- out the epsilons a bunch to give ourselves wiggle room.
          (ε-max-min , ε-wiggle , ε-max-min+ε-wiggle=ε) = split-ℚ⁺ ε
          (ε-max-min-x , ε-max-min-y , ε-max-min-split) = split-ℚ⁺ ε-max-min
          εx =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( ε-max-min-x *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
          εy =
            min-ℚ⁺
              ( one-ℚ⁺)
              ( ε-max-min-y *ℚ⁺ positive-reciprocal-rational-succ-ℕ N)
          (δ⁺@(δ , _) , δ+δ<ε-wiggle) = bound-double-le-ℚ⁺ ε-wiggle
        ((p , q) , q<p+εx , p<x , x<q) ← is-arithmetically-located-ℝ x εx
        ((r , s) , s<r+εy , r<y , y<s) ← is-arithmetically-located-ℝ y εy
        let
          p≤q = leq-lower-upper-cut-ℝ x p q p<x x<q
          r≤s = leq-lower-upper-cut-ℝ y r s r<y y<s
          q-p<εx : le-ℚ (q -ℚ p) (rational-ℚ⁺ εx)
          q-p<εx =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ q) (commutative-add-ℚ _ _) q<p+εx)
          q-p<1 =
            concatenate-le-leq-ℚ
              ( q -ℚ p)
              ( rational-ℚ⁺ εx)
              ( one-ℚ)
              ( q-p<εx)
              ( leq-left-min-ℚ⁺ _ _)
          s-r<εy : le-ℚ (s -ℚ r) (rational-ℚ⁺ εy)
          s-r<εy =
            le-transpose-right-add-ℚ _ _ _
              ( tr (le-ℚ s) (commutative-add-ℚ _ _) s<r+εy)
          s-r<1 =
            concatenate-le-leq-ℚ
              ( s -ℚ r)
              ( rational-ℚ⁺ εy)
              ( one-ℚ)
              ( s-r<εy)
              ( leq-left-min-ℚ⁺ _ _)
          max|r||s|≤sN =
            calculate-in-Poset ℚ-Poset
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)
              ≤ rational-ℕ Ny
                by
                  leq-le-ℚ
                    ( bound-Ny
                      ( (r , s) ,
                        tr
                          ( le-ℚ s)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ s-r<1) ,
                        r<y ,
                        y<s))
                in-Poset ℚ-Poset
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (right-leq-max-ℕ _ _)
                in-Poset ℚ-Poset
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
                in-Poset ℚ-Poset
          max|p||q|≤sN =
            calculate-in-Poset ℚ-Poset
            chain-of-inequalities
              max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q)
              ≤ rational-ℕ Nx
                by
                  leq-le-ℚ
                    ( bound-Nx
                      ( (p , q) ,
                        tr
                          ( le-ℚ q)
                          ( commutative-add-ℚ _ _)
                          ( le-transpose-left-diff-ℚ _ _ _ q-p<1) ,
                        p<x ,
                        x<q))
                in-Poset ℚ-Poset
              ≤ rational-ℕ N
                by preserves-leq-rational-ℕ _ _ (left-leq-max-ℕ _ _)
                in-Poset ℚ-Poset
              ≤ rational-ℕ (succ-ℕ N)
                by preserves-leq-rational-ℕ _ _ (succ-leq-ℕ N)
                in-Poset ℚ-Poset
          a = min-ℚ (min-ℚ (p *ℚ r) (p *ℚ s)) (min-ℚ (q *ℚ r) (q *ℚ s))
          b = max-ℚ (max-ℚ (p *ℚ r) (p *ℚ s)) (max-ℚ (q *ℚ r) (q *ℚ s))
        intro-exists
          (a -ℚ δ , b +ℚ δ)
          ( tr
            ( le-ℚ (b +ℚ δ))
            ( commutative-add-ℚ _ _)
            ( le-transpose-left-diff-ℚ _ _ _
              ( concatenate-leq-le-ℚ
                ( (b +ℚ δ) -ℚ (a -ℚ δ))
                ( rational-ℚ⁺ ε-max-min +ℚ (δ +ℚ δ))
                ( rational-ℚ⁺ ε)
                ( inv-tr
                  ( λ η → leq-ℚ η ( rational-ℚ⁺ ε-max-min +ℚ (δ +ℚ δ)))
                  ( ap-add-ℚ
                      ( refl)
                      ( distributive-neg-diff-ℚ _ _ ∙
                        commutative-add-ℚ _ _) ∙
                    interchange-law-add-add-ℚ _ _ _ _)
                  ( preserves-leq-left-add-ℚ _ _ _
                    ( calculate-in-Poset ℚ-Poset
                      chain-of-inequalities
                        b -ℚ a
                        ≤ ( (q -ℚ p) *ℚ
                            max-ℚ (rational-abs-ℚ r) (rational-abs-ℚ s)) +ℚ
                          ( (s -ℚ r) *ℚ
                            max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
                          by
                            bound-width-mul-interval-ℚ p q r s p≤q r≤s
                          in-Poset ℚ-Poset
                        ≤ ( rational-ℚ⁺ εx *ℚ rational-ℕ (succ-ℕ N)) +ℚ
                          ( rational-ℚ⁺ εy *ℚ rational-ℕ (succ-ℕ N))
                          by
                            preserves-leq-add-ℚ
                              ( preserves-leq-mul-ℚ⁰⁺
                                ( nonnegative-diff-leq-ℚ _ _ p≤q)
                                ( nonnegative-ℚ⁺ εx)
                                ( max-ℚ⁰⁺ (abs-ℚ r) (abs-ℚ s))
                                ( nonnegative-rational-ℕ (succ-ℕ N))
                                ( leq-le-ℚ q-p<εx)
                                ( max|r||s|≤sN))
                              ( preserves-leq-mul-ℚ⁰⁺
                                ( nonnegative-diff-leq-ℚ _ _ r≤s)
                                ( nonnegative-ℚ⁺ εy)
                                ( max-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q))
                                ( nonnegative-rational-ℕ (succ-ℕ N))
                                ( leq-le-ℚ s-r<εy)
                                ( max|p||q|≤sN))
                          in-Poset ℚ-Poset
                        ≤ ( rational-ℚ⁺ εx +ℚ rational-ℚ⁺ εy) *ℚ
                          rational-ℕ (succ-ℕ N)
                          by
                            leq-eq-ℚ _ _
                              ( inv (right-distributive-mul-add-ℚ _ _ _))
                          in-Poset ℚ-Poset
                        ≤ rational-ℚ⁺
                            ( ( ε-max-min-x *ℚ⁺
                                positive-reciprocal-rational-succ-ℕ N) +ℚ⁺
                              ( ε-max-min-y *ℚ⁺
                                positive-reciprocal-rational-succ-ℕ N)) *ℚ
                          rational-ℕ (succ-ℕ N)
                          by
                            preserves-leq-right-mul-ℚ⁰⁺
                              ( nonnegative-rational-ℕ (succ-ℕ N))
                              ( _)
                              ( _)
                              ( preserves-leq-add-ℚ
                                ( leq-right-min-ℚ⁺ _ _)
                                ( leq-right-min-ℚ⁺ _ _))
                          in-Poset ℚ-Poset
                        ≤ rational-ℚ⁺ ε-max-min
                          by
                            leq-eq-ℚ _ _
                              ( ap-mul-ℚ
                                ( inv (right-distributive-mul-add-ℚ _ _ _))
                                ( refl) ∙
                                ap
                                  ( rational-ℚ⁺)
                                  ( is-section-mul-ℚ⁺
                                    ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' N))
                                    ( ε-max-min-x +ℚ⁺ ε-max-min-y) ∙
                                    ε-max-min-split))
                          in-Poset ℚ-Poset)))
                ( tr
                  ( le-ℚ⁺ (ε-max-min +ℚ⁺ (δ⁺ +ℚ⁺ δ⁺)))
                  ( ε-max-min+ε-wiggle=ε)
                  ( preserves-le-right-add-ℚ _ _ _ δ+δ<ε-wiggle)))) ,
            intro-exists
              ( ((p , p<x) , (q , x<q)) , ((r , r<y) , (s , y<s)))
              ( le-diff-rational-ℚ⁺ a δ⁺) ,
            intro-exists
              ( ((p , p<x) , (q , x<q)) , ((r , r<y) , (s , y<s)))
              ( le-right-add-rational-ℚ⁺ b δ⁺))

  abstract
    is-located-mul-ℝ :
      is-located-lower-upper-ℝ lower-real-mul-ℝ upper-real-mul-ℝ
    is-located-mul-ℝ =
      is-located-is-arithmetically-located-lower-upper-ℝ _ _
        ( is-arithmetically-located-mul-ℝ)

  mul-ℝ : ℝ (l1 ⊔ l2)
  mul-ℝ =
    real-lower-upper-ℝ
      ( lower-real-mul-ℝ)
      ( upper-real-mul-ℝ)
      ( is-disjoint-lower-upper-cut-mul-ℝ)
      ( is-located-mul-ℝ)
```
