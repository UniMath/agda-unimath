# Multiplicative inverses of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

If a [real number](real-numbers.dedekind-real-numbers.md) `x` is
[positive](real-numbers.positive-real-numbers.md), then it has a
{{#concept "multiplicative inverse" Disambiguation="positive real numbers" Agda=inv-ℝ⁺}},
a unique, positive real number `y` such that the
[product](real-numbers.multiplication-real-numbers.md) of `x` and `y` is 1.

This definition is adapted from Lemma 11.2.4 of {{#cite UF13}}.

## Definition

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  lower-cut-inv-ℝ⁺ : subtype l ℚ
  lower-cut-inv-ℝ⁺ q =
    hom-Prop
      ( is-positive-prop-ℚ q)
      ( ∃ ℚ⁺ (λ (r , _) → upper-cut-ℝ⁺ x r ∧ le-ℚ-Prop (q *ℚ r) one-ℚ))

  upper-cut-inv-ℝ⁺ : subtype l ℚ
  upper-cut-inv-ℝ⁺ q =
    is-positive-prop-ℚ q ∧
    ∃ ℚ⁺ (λ (r , _) → lower-cut-ℝ⁺ x r ∧ le-ℚ-Prop one-ℚ (q *ℚ r))

  lower-cut-inv-ℝ⁺' : subtype l ℚ
  lower-cut-inv-ℝ⁺' q =
    Π-Prop
      ( is-positive-ℚ q)
      ( λ is-pos-q → upper-cut-ℝ⁺ x (rational-inv-ℚ⁺ (q , is-pos-q)))

  upper-cut-inv-ℝ⁺' : subtype l ℚ
  upper-cut-inv-ℝ⁺' q =
    Σ-Prop
      ( is-positive-prop-ℚ q)
      ( λ is-pos-q → lower-cut-ℝ⁺ x (rational-inv-ℚ⁺ (q , is-pos-q)))

  abstract
    leq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' :
      lower-cut-inv-ℝ⁺ ⊆ lower-cut-inv-ℝ⁺'
    leq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' q q∈L is-pos-q =
      let
        q⁺ = (q , is-pos-q)
        open do-syntax-trunc-Prop (upper-cut-ℝ⁺ x (rational-inv-ℚ⁺ q⁺))
      in do
        (r⁺@(r , _) , x<r , qr<1) ← q∈L is-pos-q
        le-upper-cut-ℝ
          ( real-ℝ⁺ x)
          ( r)
          ( rational-inv-ℚ⁺ q⁺)
          ( reflects-le-left-mul-ℚ⁺
            ( q⁺)
            ( r)
            ( rational-inv-ℚ⁺ q⁺)
            ( inv-tr
              ( le-ℚ (q *ℚ r))
              ( ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ q⁺))
              ( qr<1)))
          ( x<r)

    leq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' :
      upper-cut-inv-ℝ⁺ ⊆ upper-cut-inv-ℝ⁺'
    leq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' q (is-pos-q , ∃r) =
      ( is-pos-q ,
        let
          q⁺ = (q , is-pos-q)
          open do-syntax-trunc-Prop (lower-cut-ℝ⁺ x (rational-inv-ℚ⁺ q⁺))
        in do
          (r⁺@(r , _) , r<x , 1<qr) ← ∃r
          le-lower-cut-ℝ
            ( real-ℝ⁺ x)
            ( rational-inv-ℚ⁺ q⁺)
            ( r)
            ( reflects-le-left-mul-ℚ⁺
              ( q⁺)
              ( rational-inv-ℚ⁺ q⁺)
              ( r)
              ( inv-tr
                ( λ s → le-ℚ s (q *ℚ r))
                ( ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ q⁺))
                ( 1<qr)))
            ( r<x))

    leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺ :
      lower-cut-inv-ℝ⁺' ⊆ lower-cut-inv-ℝ⁺
    leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺ q q∈L' is-pos-q =
      let
        q⁺ = (q , is-pos-q)
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ⁺ (λ (r , _) → upper-cut-ℝ⁺ x r ∧ le-ℚ-Prop (q *ℚ r) one-ℚ))
      in do
        (r , r<q⁻¹ , x<r) ←
          forward-implication
            ( is-rounded-upper-cut-ℝ⁺ x (rational-inv-ℚ⁺ q⁺))
            ( q∈L' is-pos-q)
        intro-exists
          ( r , is-positive-is-in-upper-cut-ℝ⁺ x r x<r)
          ( x<r ,
            tr
              ( le-ℚ (q *ℚ r))
              ( ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ q⁺))
              ( preserves-le-left-mul-ℚ⁺ q⁺ r (rational-inv-ℚ⁺ q⁺) r<q⁻¹))

    leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺ :
      upper-cut-inv-ℝ⁺' ⊆ upper-cut-inv-ℝ⁺
    leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺ q (is-pos-q , q⁻¹<x) =
      ( is-pos-q ,
        let
          q⁺ = (q , is-pos-q)
          open
            do-syntax-trunc-Prop
              ( ∃ ℚ⁺ λ (r , _) → lower-cut-ℝ⁺ x r ∧ le-ℚ-Prop one-ℚ (q *ℚ r))
        in do
          (r , q⁻¹<r , r<x) ←
            forward-implication
              ( is-rounded-lower-cut-ℝ⁺ x (rational-inv-ℚ⁺ q⁺))
              ( q⁻¹<x)
          intro-exists
            ( r , is-positive-le-ℚ⁺ (inv-ℚ⁺ q⁺) r q⁻¹<r)
            ( r<x ,
              tr
                ( λ s → le-ℚ s (q *ℚ r))
                ( ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ q⁺))
                ( preserves-le-left-mul-ℚ⁺ q⁺ (rational-inv-ℚ⁺ q⁺) r q⁻¹<r)))

    eq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' :
      lower-cut-inv-ℝ⁺ ＝ lower-cut-inv-ℝ⁺'
    eq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' =
      antisymmetric-leq-subtype _ _
        ( leq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺')
        ( leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺)

    eq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' :
      upper-cut-inv-ℝ⁺ ＝ upper-cut-inv-ℝ⁺'
    eq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' =
      antisymmetric-leq-subtype _ _
        ( leq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺')
        ( leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺)

  abstract
    exists-positive-ℚ-lower-cut-inv-ℝ⁺ :
      exists ℚ⁺ (lower-cut-inv-ℝ⁺ ∘ rational-ℚ⁺)
    exists-positive-ℚ-lower-cut-inv-ℝ⁺ =
      let open do-syntax-trunc-Prop (∃ ℚ⁺ (lower-cut-inv-ℝ⁺ ∘ rational-ℚ⁺))
      in do
        (q , x<q) ← is-inhabited-upper-cut-ℝ⁺ x
        let q⁺ = (q , is-positive-is-in-upper-cut-ℝ⁺ x q x<q)
        intro-exists
          ( inv-ℚ⁺ q⁺)
          ( leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺
            ( _)
            ( λ _ →
              inv-tr
                ( is-in-upper-cut-ℝ⁺ x)
                ( ( ap
                    ( rational-inv-ℚ⁺)
                    ( eq-type-subtype is-positive-prop-ℚ refl)) ∙
                  ( ap rational-ℚ⁺ (inv-inv-ℚ⁺ q⁺)))
                ( x<q)))

    is-inhabited-lower-cut-inv-ℝ⁺ : is-inhabited-subtype lower-cut-inv-ℝ⁺
    is-inhabited-lower-cut-inv-ℝ⁺ =
      map-exists
        ( is-in-subtype lower-cut-inv-ℝ⁺)
        ( rational-ℚ⁺)
        ( λ _ → id)
        ( exists-positive-ℚ-lower-cut-inv-ℝ⁺)

    is-inhabited-upper-cut-inv-ℝ⁺ : is-inhabited-subtype upper-cut-inv-ℝ⁺
    is-inhabited-upper-cut-inv-ℝ⁺ =
      let
        open
          do-syntax-trunc-Prop (is-inhabited-subtype-Prop upper-cut-inv-ℝ⁺)
      in do
        (q⁺ , q⁺<x) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ x
        intro-exists
          ( rational-inv-ℚ⁺ q⁺)
          ( leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺ _
            ( is-positive-rational-inv-ℚ⁺ q⁺ ,
              inv-tr
                ( is-in-lower-cut-ℝ⁺ x)
                ( ( ap
                    ( rational-inv-ℚ⁺)
                    ( eq-type-subtype is-positive-prop-ℚ refl)) ∙
                  ( ap rational-ℚ⁺ (inv-inv-ℚ⁺ q⁺)))
                q⁺<x))

    forward-implication-is-rounded-lower-cut-inv-ℝ⁺ :
      (q : ℚ) → is-in-subtype lower-cut-inv-ℝ⁺ q →
      exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-inv-ℝ⁺ r))
    forward-implication-is-rounded-lower-cut-inv-ℝ⁺ q q∈L =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-inv-ℝ⁺ r)))
      in
        rec-coproduct
          ( λ is-pos-q →
            do
              (r⁺@(r , is-pos-r) , x<r , qr<1) ← q∈L is-pos-q
              (r' , r'<r , x<r') ←
                forward-implication (is-rounded-upper-cut-ℝ⁺ x r) x<r
              let
                r⁻¹ = inv-ℚ⁺ r⁺
                r'⁺ = (r' , is-positive-is-in-upper-cut-ℝ⁺ x r' x<r')
                r'⁻¹ = inv-ℚ⁺ r'⁺
              intro-exists
                ( rational-ℚ⁺ r'⁻¹)
                ( transitive-le-ℚ
                    ( q)
                    ( rational-ℚ⁺ r⁻¹)
                    ( rational-ℚ⁺ r'⁻¹)
                    ( inv-le-ℚ⁺ _ _ r'<r)
                    ( binary-tr
                      ( le-ℚ)
                      ( is-retraction-right-div-ℚ⁺ r⁺ q)
                      ( left-unit-law-mul-ℚ _)
                      ( preserves-le-right-mul-ℚ⁺ r⁻¹ (q *ℚ r) one-ℚ qr<1)) ,
                  leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺ _
                    ( λ _ →
                      inv-tr
                        ( is-in-upper-cut-ℝ⁺ x)
                        ( ( ap
                            ( rational-inv-ℚ⁺)
                            ( eq-type-subtype is-positive-prop-ℚ refl)) ∙
                          ( ap rational-ℚ⁺ (inv-inv-ℚ⁺ r'⁺)))
                        ( x<r'))))
          ( λ is-nonpos-q →
            do
              (r⁺@(r , _) , r∈L) ← exists-positive-ℚ-lower-cut-inv-ℝ⁺
              intro-exists
                ( r)
                ( le-nonpositive-positive-ℚ (q , is-nonpos-q) r⁺ , r∈L))
          ( decide-is-positive-is-nonpositive-ℚ q)

    backward-implication-is-rounded-lower-cut-inv-ℝ⁺ :
      (q : ℚ) → exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-inv-ℝ⁺ r)) →
      is-in-subtype lower-cut-inv-ℝ⁺ q
    backward-implication-is-rounded-lower-cut-inv-ℝ⁺ q ∃q' is-pos-q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ⁺ (λ (r , _) → upper-cut-ℝ⁺ x r ∧ le-ℚ-Prop (q *ℚ r) one-ℚ))
      in do
        (q' , q<q' , q'∈L) ← ∃q'
        (r'⁺@(r' , _) , x<r' , q'r'<1) ←
          q'∈L (is-positive-le-ℚ⁺ (q , is-pos-q) q' q<q')
        intro-exists
          ( r'⁺)
          ( x<r' ,
            transitive-le-ℚ
              ( q *ℚ r')
              ( q' *ℚ r')
              ( one-ℚ)
              ( q'r'<1)
              ( preserves-le-right-mul-ℚ⁺ r'⁺ q q' q<q'))

    is-rounded-lower-cut-inv-ℝ⁺ :
      (q : ℚ) →
      ( is-in-subtype lower-cut-inv-ℝ⁺ q ↔
        exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-inv-ℝ⁺ r)))
    is-rounded-lower-cut-inv-ℝ⁺ q =
      ( forward-implication-is-rounded-lower-cut-inv-ℝ⁺ q ,
        backward-implication-is-rounded-lower-cut-inv-ℝ⁺ q)

    forward-implication-is-rounded-upper-cut-inv-ℝ⁺ :
      (q : ℚ) → is-in-subtype upper-cut-inv-ℝ⁺ q →
      exists ℚ (λ r → (le-ℚ-Prop r q) ∧ (upper-cut-inv-ℝ⁺ r))
    forward-implication-is-rounded-upper-cut-inv-ℝ⁺ q (is-pos-q , ∃r) =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ q' → le-ℚ-Prop q' q ∧ upper-cut-inv-ℝ⁺ q'))
      in do
        (r⁺@(r , _) , r<x , 1<qr) ← ∃r
        (r' , r<r' , r'<x) ←
          forward-implication (is-rounded-lower-cut-ℝ⁺ x r) r<x
        let r'⁺ = (r' , is-positive-le-ℚ⁺ r⁺ r' r<r')
        intro-exists
          ( rational-ℚ⁺ (inv-ℚ⁺ r'⁺))
          ( transitive-le-ℚ
              ( rational-ℚ⁺ (inv-ℚ⁺ r'⁺))
              ( rational-ℚ⁺ (inv-ℚ⁺ r⁺))
              ( q)
              ( binary-tr
                ( le-ℚ)
                ( left-unit-law-mul-ℚ _)
                ( is-retraction-right-div-ℚ⁺ r⁺ q)
                ( preserves-le-right-mul-ℚ⁺ (inv-ℚ⁺ r⁺) one-ℚ (q *ℚ r) 1<qr))
              ( inv-le-ℚ⁺ _ _ r<r') ,
            leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺ _
              ( is-positive-rational-inv-ℚ⁺ r'⁺ ,
                inv-tr
                  ( is-in-lower-cut-ℝ⁺ x)
                  ( ( ap
                      ( rational-inv-ℚ⁺)
                      ( eq-type-subtype is-positive-prop-ℚ refl)) ∙
                    ( ap rational-ℚ⁺ (inv-inv-ℚ⁺ r'⁺)))
                  ( r'<x)))

    backward-implication-is-rounded-upper-cut-inv-ℝ⁺ :
      (q : ℚ) →
      exists ℚ (λ r → (le-ℚ-Prop r q) ∧ (upper-cut-inv-ℝ⁺ r)) →
      is-in-subtype upper-cut-inv-ℝ⁺ q
    backward-implication-is-rounded-upper-cut-inv-ℝ⁺ q ∃q' =
      let open do-syntax-trunc-Prop (upper-cut-inv-ℝ⁺ q)
      in do
        (q' , q'<q , is-pos-q' , ∃r') ← ∃q'
        (r'⁺@(r' , _) , x<r' , 1<q'r') ← ∃r'
        ( is-positive-le-ℚ⁺ (q' , is-pos-q') q q'<q ,
          intro-exists
            ( r'⁺)
            ( x<r' ,
              transitive-le-ℚ
                ( one-ℚ)
                ( q' *ℚ r')
                ( q *ℚ r')
                ( preserves-le-right-mul-ℚ⁺ r'⁺ q' q q'<q)
                ( 1<q'r')))

    is-rounded-upper-cut-inv-ℝ⁺ :
      (q : ℚ) →
      ( is-in-subtype upper-cut-inv-ℝ⁺ q ↔
        exists ℚ (λ r → (le-ℚ-Prop r q) ∧ (upper-cut-inv-ℝ⁺ r)))
    is-rounded-upper-cut-inv-ℝ⁺ q =
      ( forward-implication-is-rounded-upper-cut-inv-ℝ⁺ q ,
        backward-implication-is-rounded-upper-cut-inv-ℝ⁺ q)

    is-disjoint-lower-upper-cut-inv-ℝ⁺ :
      disjoint-subtype lower-cut-inv-ℝ⁺ upper-cut-inv-ℝ⁺
    is-disjoint-lower-upper-cut-inv-ℝ⁺ q (q∈L , is-pos-q , ∃rᵤ:1<qrᵤ) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        ((rᵤ , _) , rᵤ<x , 1<qrᵤ) ← ∃rᵤ:1<qrᵤ
        ((rₗ , _) , x<rₗ , qrₗ<1) ← q∈L is-pos-q
        asymmetric-le-ℚ rₗ rᵤ
          ( reflects-le-left-mul-ℚ⁺
            ( q , is-pos-q)
            ( _)
            ( _)
            ( transitive-le-ℚ (q *ℚ rₗ) one-ℚ (q *ℚ rᵤ) 1<qrᵤ qrₗ<1))
          ( le-lower-upper-cut-ℝ⁺ x rᵤ rₗ rᵤ<x x<rₗ)

    is-located-lower-upper-cut-inv-ℝ⁺ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop (lower-cut-inv-ℝ⁺ p) (upper-cut-inv-ℝ⁺ q)
    is-located-lower-upper-cut-inv-ℝ⁺ p q p<q =
      rec-coproduct
        ( λ is-pos-p →
          let
            p⁺ = (p , is-pos-p)
            is-pos-q = is-positive-le-ℚ⁺ p⁺ q p<q
            q⁺ = (q , is-pos-q)
          in
            elim-disjunction
              ( lower-cut-inv-ℝ⁺ p ∨ upper-cut-inv-ℝ⁺ q)
              ( λ q⁻¹<x →
                inr-disjunction
                  ( leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺ _
                    ( is-pos-q , q⁻¹<x)))
              ( λ x<p⁻¹ →
                inl-disjunction
                  ( leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺ _
                    ( λ _ →
                      tr
                        ( is-in-upper-cut-ℝ⁺ x ∘ rational-inv-ℚ⁺)
                        ( eq-type-subtype is-positive-prop-ℚ refl)
                        ( x<p⁻¹))))
              ( is-located-lower-upper-cut-ℝ
                ( real-ℝ⁺ x)
                ( rational-ℚ⁺ (inv-ℚ⁺ q⁺))
                ( rational-ℚ⁺ (inv-ℚ⁺ p⁺))
                ( inv-le-ℚ⁺ p⁺ q⁺ p<q)))
        ( λ is-nonpos-p →
          inl-disjunction
            ( ex-falso ∘ not-is-positive-is-nonpositive-ℚ is-nonpos-p))
        ( decide-is-positive-is-nonpositive-ℚ p)

  opaque
    real-inv-ℝ⁺ : ℝ l
    real-inv-ℝ⁺ =
      ( ( lower-cut-inv-ℝ⁺ ,
          is-inhabited-lower-cut-inv-ℝ⁺ ,
          is-rounded-lower-cut-inv-ℝ⁺) ,
        ( upper-cut-inv-ℝ⁺ ,
          is-inhabited-upper-cut-inv-ℝ⁺ ,
          is-rounded-upper-cut-inv-ℝ⁺) ,
        is-disjoint-lower-upper-cut-inv-ℝ⁺ ,
        is-located-lower-upper-cut-inv-ℝ⁺)
```
