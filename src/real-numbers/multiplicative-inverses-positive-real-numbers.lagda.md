# Multiplicative inverses of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-positive-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
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
open import real-numbers.enclosing-closed-rational-intervals-real-numbers
open import real-numbers.inequality-positive-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-positive-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-positive-real-numbers
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
    exists-ℚ⁺-in-lower-cut-inv-ℝ⁺ :
      exists ℚ⁺ (lower-cut-inv-ℝ⁺ ∘ rational-ℚ⁺)
    exists-ℚ⁺-in-lower-cut-inv-ℝ⁺ =
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
        ( exists-ℚ⁺-in-lower-cut-inv-ℝ⁺)

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
              (r⁺@(r , _) , r∈L) ← exists-ℚ⁺-in-lower-cut-inv-ℝ⁺
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
      is-in-subtype lower-cut-inv-ℝ⁺ q ↔
      exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-inv-ℝ⁺ r))
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
                ( inv-le-ℚ⁺ p⁺ q⁺ p<q)))
        ( λ is-nonpos-p →
          inl-disjunction
            ( λ is-pos-p →
              ex-falso
                ( is-not-positive-and-nonpositive-ℚ (is-pos-p , is-nonpos-p))))
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

## Properties

### The multiplicative inverse of a positive real number is positive

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  opaque
    unfolding real-inv-ℝ⁺

    is-positive-inv-ℝ⁺ : is-positive-ℝ (real-inv-ℝ⁺ x)
    is-positive-inv-ℝ⁺ =
      is-positive-zero-in-lower-cut-ℝ
        ( real-inv-ℝ⁺ x)
        ( ex-falso ∘ is-not-positive-zero-ℚ)

  inv-ℝ⁺ : ℝ⁺ l
  inv-ℝ⁺ = (real-inv-ℝ⁺ x , is-positive-inv-ℝ⁺)
```

### The multiplicative inverse is a multiplicative inverse

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  opaque
    unfolding leq-ℝ leq-ℝ' mul-ℝ real-inv-ℝ⁺ real-ℚ

    one-is-in-interval-right-inverse-law-mul-ℝ⁺ :
      ([a,b] [c,d] : closed-interval-ℚ) →
      is-enclosing-closed-rational-interval-ℝ (real-ℝ⁺ x) [a,b] →
      is-enclosing-closed-rational-interval-ℝ (real-inv-ℝ⁺ x) [c,d] →
      is-positive-ℚ (lower-bound-closed-interval-ℚ [a,b]) →
      is-positive-ℚ (lower-bound-closed-interval-ℚ [c,d]) →
      is-in-closed-interval-ℚ
        ( mul-closed-interval-ℚ [a,b] [c,d])
        ( one-ℚ)
    one-is-in-interval-right-inverse-law-mul-ℝ⁺
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) (a<x , x<b) (c<x⁻¹ , x⁻¹<d)
      is-pos-a is-pos-c =
      let
        is-pos-b = is-positive-is-in-upper-cut-ℝ⁺ x b x<b
        (is-pos-d , d⁻¹<x) =
          leq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' x d x⁻¹<d
        d⁺ = (d , is-pos-d)
        a' = max-ℚ a (rational-inv-ℚ⁺ d⁺)
        a'<x =
          is-in-lower-cut-max-ℚ (real-ℝ⁺ x) a (rational-inv-ℚ⁺ d⁺) a<x d⁻¹<x
        is-pos-a' =
          is-positive-leq-ℚ⁺ (inv-ℚ⁺ d⁺) a' (leq-right-max-ℚ _ _)
        a'⁺ = (a' , is-pos-a')
        c⁺ = (c , is-pos-c)
        x<c⁻¹ : is-in-upper-cut-ℝ⁺ x (rational-inv-ℚ⁺ c⁺)
        x<c⁻¹ =
          leq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' x c c<x⁻¹ is-pos-c
        a'⁻¹≤d =
          tr
            ( leq-ℚ (rational-inv-ℚ⁺ a'⁺))
            ( rational-inv-inv-ℚ⁺ d⁺)
            ( inv-leq-ℚ⁺ (inv-ℚ⁺ d⁺) a'⁺ (leq-right-max-ℚ _ _))
        c≤a'⁻¹ =
          tr
            ( λ r → leq-ℚ r (rational-inv-ℚ⁺ a'⁺))
            ( rational-inv-inv-ℚ⁺ c⁺)
            ( inv-leq-ℚ⁺
              ( a'⁺)
              ( inv-ℚ⁺ c⁺)
              ( leq-lower-upper-cut-ℝ
                ( real-ℝ⁺ x)
                ( a')
                ( rational-inv-ℚ⁺ c⁺)
                ( a'<x)
                ( x<c⁻¹)))
      in
        tr
          ( is-in-closed-interval-ℚ
            ( mul-closed-interval-ℚ [a,b] [c,d]))
          ( ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ a'⁺))
          ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
            ( [a,b])
            ( [c,d])
            ( a')
            ( rational-inv-ℚ⁺ a'⁺)
            ( leq-left-max-ℚ _ _ ,
              leq-lower-upper-cut-ℝ (real-ℝ⁺ x) a' b a'<x x<b)
            ( c≤a'⁻¹ , a'⁻¹≤d))

    leq-real-right-inverse-law-mul-ℝ⁺ :
      leq-ℝ (real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x) one-ℝ
    leq-real-right-inverse-law-mul-ℝ⁺ q q<xx⁻¹ =
      let open do-syntax-trunc-Prop (le-ℚ-Prop q one-ℚ)
      in do
        ( ( ([a,b]@((a , b) , a≤b) , a<x , x<b) ,
            ([c,d]@((c , d) , c≤d) , c<x⁻¹ , x⁻¹<d)) ,
          q<[a,b][c,d]) ← q<xx⁻¹
        let
          is-pos-b = is-positive-is-in-upper-cut-ℝ⁺ x b x<b
          (is-pos-d , d⁻¹<x) =
            leq-upper-cut-inv-ℝ⁺-upper-cut-inv-ℝ⁺' x d x⁻¹<d
          case-is-nonpos-a is-nonpos-a =
            le-nonpositive-positive-ℚ
              ( q ,
                is-nonpositive-leq-ℚ⁰⁻
                  ( mul-nonpositive-positive-ℚ (a , is-nonpos-a) (d , is-pos-d))
                  ( q)
                  ( transitive-leq-ℚ
                    ( q)
                    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                    ( a *ℚ d)
                    ( transitive-leq-ℚ _ _ _
                      ( leq-right-min-ℚ _ _)
                      ( leq-left-min-ℚ _ _))
                    ( leq-le-ℚ q<[a,b][c,d])))
              ( one-ℚ⁺)
          case-is-nonpos-c is-nonpos-c =
            le-nonpositive-positive-ℚ
              ( q ,
                is-nonpositive-leq-ℚ⁰⁻
                  ( mul-positive-nonpositive-ℚ
                    ( b , is-pos-b)
                    ( c , is-nonpos-c))
                  ( q)
                  ( transitive-leq-ℚ
                    ( q)
                    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                    ( b *ℚ c)
                    ( transitive-leq-ℚ _ _ _
                      ( leq-left-min-ℚ _ _)
                      ( leq-right-min-ℚ _ _))
                    ( leq-le-ℚ q<[a,b][c,d])))
              ( one-ℚ⁺)
          case-is-pos-a-c : is-positive-ℚ a → is-positive-ℚ c → le-ℚ q one-ℚ
          case-is-pos-a-c is-pos-a is-pos-c =
            concatenate-le-leq-ℚ
              ( q)
              ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( one-ℚ)
              ( q<[a,b][c,d])
              ( pr1
                ( one-is-in-interval-right-inverse-law-mul-ℝ⁺
                  ( [a,b])
                  ( [c,d])
                  ( a<x , x<b)
                  ( c<x⁻¹ , x⁻¹<d)
                  ( is-pos-a)
                  ( is-pos-c)))
        rec-coproduct
          ( λ is-pos-a →
            rec-coproduct
              ( case-is-pos-a-c is-pos-a)
              ( case-is-nonpos-c)
              ( decide-is-positive-is-nonpositive-ℚ c))
          ( case-is-nonpos-a)
          ( decide-is-positive-is-nonpositive-ℚ a)

    leq-real-right-inverse-law-mul-ℝ⁺' :
      leq-ℝ one-ℝ (real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x)
    leq-real-right-inverse-law-mul-ℝ⁺' =
      leq-leq'-ℝ one-ℝ (real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x)
        ( λ q xx⁻¹<q →
          let
            open do-syntax-trunc-Prop (le-ℚ-Prop one-ℚ q)
          in do
            ( ( ([a,b]@((a , b) , a≤b) , a<x , x<b) ,
                ([c,d]@((c , d) , c≤d) , c<x⁻¹ , x⁻¹<d)) ,
              [a,b][c,d]<q) ← xx⁻¹<q
            (a'⁺@(a' , is-pos-a') , a'<x) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ x
            (c'⁺@(c' , is-pos-c') , c'<x⁻¹) ← exists-ℚ⁺-in-lower-cut-inv-ℝ⁺ x
            let
              a'' = max-ℚ a a'
              is-pos-a'' = is-positive-leq-ℚ⁺ a'⁺ a'' (leq-right-max-ℚ _ _)
              a''<x = is-in-lower-cut-max-ℚ (real-ℝ⁺ x) a a' a<x a'<x
              c'' = max-ℚ c c'
              is-pos-c'' = is-positive-leq-ℚ⁺ c'⁺ c'' (leq-right-max-ℚ _ _)
              c''<x⁻¹ = is-in-lower-cut-max-ℚ (real-inv-ℝ⁺ x) c c' c<x⁻¹ c'<x⁻¹
              [a'',b] =
                ( (a'' , b) , leq-lower-upper-cut-ℝ (real-ℝ⁺ x) a'' b a''<x x<b)
              [c'',d] =
                ( (c'' , d) ,
                  leq-lower-upper-cut-ℝ (real-inv-ℝ⁺ x) c'' d c''<x⁻¹ x⁻¹<d)
            concatenate-leq-le-ℚ
              ( one-ℚ)
              ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( q)
              ( transitive-leq-ℚ
                ( one-ℚ)
                ( upper-bound-mul-closed-interval-ℚ [a'',b] [c'',d])
                ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
                ( pr2
                  ( preserves-leq-mul-closed-interval-ℚ
                    ( [a'',b])
                    ( [a,b])
                    ( [c'',d])
                    ( [c,d])
                    ( leq-left-max-ℚ _ _ , refl-leq-ℚ b)
                    ( leq-left-max-ℚ _ _ , refl-leq-ℚ d)))
                ( pr2
                  ( one-is-in-interval-right-inverse-law-mul-ℝ⁺
                    ( [a'',b])
                    ( [c'',d])
                    ( a''<x , x<b)
                    ( c''<x⁻¹ , x⁻¹<d)
                    ( is-pos-a'')
                    ( is-pos-c''))))
              ( [a,b][c,d]<q))

  abstract
    right-inverse-law-mul-ℝ⁺ : sim-ℝ (real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x) one-ℝ
    right-inverse-law-mul-ℝ⁺ =
      sim-sim-leq-ℝ
        ( leq-real-right-inverse-law-mul-ℝ⁺ ,
          leq-real-right-inverse-law-mul-ℝ⁺')

    left-inverse-law-mul-ℝ⁺ : sim-ℝ (real-inv-ℝ⁺ x *ℝ real-ℝ⁺ x) one-ℝ
    left-inverse-law-mul-ℝ⁺ =
      tr
        ( λ y → sim-ℝ y one-ℝ)
        ( commutative-mul-ℝ _ _)
        ( right-inverse-law-mul-ℝ⁺)
```

### The multiplicative inverse operation preserves similarity

```agda
opaque
  unfolding leq-ℝ leq-ℝ' real-inv-ℝ⁺ sim-ℝ

  preserves-sim-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → sim-ℝ⁺ x y →
    sim-ℝ⁺ (inv-ℝ⁺ x) (inv-ℝ⁺ y)
  preserves-sim-inv-ℝ⁺ (x , _) (y , _) (Lx⊆Ly , Ly⊆Lx) =
    ( ( λ q q<x⁻¹ is-pos-q →
        map-tot-exists
          ( λ (r , _) (x<r , qr<1) → (leq'-leq-ℝ y x Ly⊆Lx r x<r , qr<1))
          ( q<x⁻¹ is-pos-q)) ,
      λ q q<y⁻¹ is-pos-q →
        map-tot-exists
          ( λ (r , _) (y<r , qr<1) → (leq'-leq-ℝ x y Lx⊆Ly r y<r , qr<1))
          ( q<y⁻¹ is-pos-q))
```

### The multiplicative inverse operation reverses strict inequality

```agda
opaque
  unfolding le-ℝ real-inv-ℝ⁺

  inv-le-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → le-ℝ⁺ x y →
    le-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-le-ℝ⁺ x y x<y =
    let open do-syntax-trunc-Prop (le-prop-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x))
    in do
      (q , x<q , q<y) ← x<y
      let q⁺ = (q , is-positive-is-in-upper-cut-ℝ⁺ x q x<q)
      intro-exists
        ( rational-inv-ℚ⁺ q⁺)
        ( leq-upper-cut-inv-ℝ⁺'-upper-cut-inv-ℝ⁺
          ( y)
          ( rational-inv-ℚ⁺ q⁺)
          ( is-positive-rational-inv-ℚ⁺ q⁺ ,
            inv-tr
              ( is-in-lower-cut-ℝ⁺ y)
              ( rational-inv-inv-ℚ⁺ q⁺)
              ( q<y)) ,
          leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺
            ( x)
            ( rational-inv-ℚ⁺ q⁺)
            ( λ _ →
              inv-tr
                ( is-in-upper-cut-ℝ⁺ x)
                ( ( ap
                    ( rational-inv-ℚ⁺)
                    ( eq-type-subtype is-positive-prop-ℚ refl)) ∙
                  ( ap rational-ℚ⁺ (inv-inv-ℚ⁺ q⁺)))
                ( x<q)))
```

### The multiplicative inverse reverses inequality

```agda
opaque
  unfolding leq-ℝ leq-ℝ' real-inv-ℝ⁺

  inv-leq-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → leq-ℝ⁺ x y →
    leq-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-leq-ℝ⁺ x⁺@(x , _) y⁺@(y , _) x≤y q q<y⁻¹ =
    leq-lower-cut-inv-ℝ⁺'-lower-cut-inv-ℝ⁺
      ( x⁺)
      ( q)
      ( λ is-pos-q →
        leq'-leq-ℝ x y x≤y
          ( rational-inv-ℚ⁺ (q , is-pos-q))
          ( leq-lower-cut-inv-ℝ⁺-lower-cut-inv-ℝ⁺' y⁺ q q<y⁻¹ is-pos-q))
```

### Multiplication by a positive real number is an automorphism of the real numbers

```agda
abstract
  cancel-left-div-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) →
    sim-ℝ (real-inv-ℝ⁺ x *ℝ (real-ℝ⁺ x *ℝ y)) y
  cancel-left-div-mul-ℝ⁺ x⁺@(x , _) y =
    similarity-reasoning-ℝ
      real-inv-ℝ⁺ x⁺ *ℝ (x *ℝ y)
      ~ℝ (real-inv-ℝ⁺ x⁺ *ℝ x) *ℝ y
        by sim-eq-ℝ (inv (associative-mul-ℝ _ _ _))
      ~ℝ one-ℝ *ℝ y
        by preserves-sim-right-mul-ℝ y _ _ (left-inverse-law-mul-ℝ⁺ x⁺)
      ~ℝ y
        by sim-eq-ℝ (left-unit-law-mul-ℝ y)

  cancel-left-mul-div-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) →
    sim-ℝ (real-ℝ⁺ x *ℝ (real-inv-ℝ⁺ x *ℝ y)) y
  cancel-left-mul-div-ℝ⁺ x⁺@(x , _) y =
    similarity-reasoning-ℝ
      x *ℝ (real-inv-ℝ⁺ x⁺ *ℝ y)
      ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ y
        by sim-eq-ℝ (inv (associative-mul-ℝ _ _ _))
      ~ℝ one-ℝ *ℝ y
        by preserves-sim-right-mul-ℝ y _ _ (right-inverse-law-mul-ℝ⁺ x⁺)
      ~ℝ y
        by sim-eq-ℝ (left-unit-law-mul-ℝ y)

is-equiv-left-mul-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) → is-equiv (λ (y : ℝ l) → real-ℝ⁺ x *ℝ y)
is-equiv-left-mul-ℝ⁺ x =
  is-equiv-is-invertible
    ( real-inv-ℝ⁺ x *ℝ_)
    ( λ y → eq-sim-ℝ (cancel-left-mul-div-ℝ⁺ x y))
    ( λ y → eq-sim-ℝ (cancel-left-div-mul-ℝ⁺ x y))

aut-left-mul-ℝ⁺ : (l : Level) → ℝ⁺ l → Aut (ℝ l)
aut-left-mul-ℝ⁺ l x = (real-ℝ⁺ x *ℝ_ , is-equiv-left-mul-ℝ⁺ x)
```
