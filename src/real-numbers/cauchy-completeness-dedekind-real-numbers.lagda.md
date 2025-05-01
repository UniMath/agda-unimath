# Cauchy completeness of the Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cauchy-completeness-dedekind-real-numbers where
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
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
[metric space of the Dedekind real numbers](real-numbers.metric-space-of-real-numbers.md)
is [complete](metric-spaces.complete-metric-spaces.md).

## Definitions

### Cauchy approximations in the real numbers

```agda
cauchy-approximation-leq-ℝ : (l : Level) → UU (lsuc l)
cauchy-approximation-leq-ℝ l =
  cauchy-approximation-Metric-Space (metric-space-leq-ℝ l)

map-cauchy-approximation-leq-ℝ :
  {l : Level} → (x : cauchy-approximation-leq-ℝ l) → ℚ⁺ → ℝ l
map-cauchy-approximation-leq-ℝ {l} =
  map-cauchy-approximation-Metric-Space (metric-space-leq-ℝ l)

is-cauchy-map-cauchy-approximation-leq-ℝ :
  {l : Level} → (x : cauchy-approximation-leq-ℝ l) →
  (ε δ : ℚ⁺) →
  neighborhood-Metric-Space
    ( metric-space-leq-ℝ l)
    ( ε +ℚ⁺ δ)
    ( map-cauchy-approximation-leq-ℝ x ε)
    ( map-cauchy-approximation-leq-ℝ x δ)
is-cauchy-map-cauchy-approximation-leq-ℝ {l} x =
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space
    ( metric-space-leq-ℝ l)
    ( x)
```

## Properties

### The limit of a Cauchy sequence

```agda
module _
  {l : Level} (x : cauchy-approximation-leq-ℝ l)
  where

  lower-cut-lim-cauchy-approximation-leq-ℝ : subtype l ℚ
  lower-cut-lim-cauchy-approximation-leq-ℝ q =
    ∃ ( ℚ⁺ × ℚ⁺)
      ( λ (ε , θ) →
        lower-cut-ℝ
          ( map-cauchy-approximation-leq-ℝ x ε)
          ( q +ℚ rational-ℚ⁺ (ε +ℚ⁺ θ)))

  upper-cut-lim-cauchy-approximation-leq-ℝ : subtype l ℚ
  upper-cut-lim-cauchy-approximation-leq-ℝ q =
    ∃ ( ℚ⁺ × ℚ⁺)
      ( λ (ε , θ) →
        upper-cut-ℝ
          ( map-cauchy-approximation-leq-ℝ x ε)
          ( q -ℚ (rational-ℚ⁺ (ε +ℚ⁺ θ))))

  abstract
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ :
      exists ℚ lower-cut-lim-cauchy-approximation-leq-ℝ
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ =
      let
        open do-syntax-trunc-Prop (∃ ℚ lower-cut-lim-cauchy-approximation-leq-ℝ)
        x1 = map-cauchy-approximation-leq-ℝ x one-ℚ⁺
        two-ℚ = one-ℚ +ℚ one-ℚ
      in do
        p , p<x1 ← is-inhabited-lower-cut-ℝ x1
        intro-exists
          ( p -ℚ two-ℚ)
          ( intro-exists
            ( one-ℚ⁺ , one-ℚ⁺)
            ( inv-tr
              ( is-in-lower-cut-ℝ x1)
              ( is-section-diff-ℚ two-ℚ p)
              ( p<x1)))

    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ :
      exists ℚ upper-cut-lim-cauchy-approximation-leq-ℝ
    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ =
      let
        open do-syntax-trunc-Prop (∃ ℚ upper-cut-lim-cauchy-approximation-leq-ℝ)
        x1 = map-cauchy-approximation-leq-ℝ x one-ℚ⁺
        two-ℚ = one-ℚ +ℚ one-ℚ
      in do
        q , x1<q ← is-inhabited-upper-cut-ℝ x1
        intro-exists
          ( q +ℚ two-ℚ)
          ( intro-exists
            ( one-ℚ⁺ , one-ℚ⁺)
            ( inv-tr
              ( is-in-upper-cut-ℝ x1)
              ( is-retraction-diff-ℚ two-ℚ q)
              ( x1<q)))

    forward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q →
      exists
        ( ℚ)
        ( λ r → le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r)
    forward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ
      q q<lim =
        let
          open
            do-syntax-trunc-Prop
              ( ∃
                ( ℚ)
                ( λ r →
                  le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r))
        in do
          (ε⁺@(ε , _) , θ⁺@(θ , _)) , q+ε+θ<xε ← q<lim
          let xε = map-cauchy-approximation-leq-ℝ x ε⁺
          r , q+ε+θ<r , r<xε ←
            forward-implication
              ( is-rounded-lower-cut-ℝ
                ( map-cauchy-approximation-leq-ℝ x ε⁺)
                ( q +ℚ (ε +ℚ θ)))
              ( q+ε+θ<xε)
          intro-exists
            ( r -ℚ (ε +ℚ θ))
            ( le-transpose-left-add-ℚ q (ε +ℚ θ) r q+ε+θ<r ,
              intro-exists
                ( ε⁺ , θ⁺)
                ( inv-tr
                  ( is-in-lower-cut-ℝ xε)
                  ( is-section-diff-ℚ (ε +ℚ θ) r)
                  ( r<xε)))

    backward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      exists
        ( ℚ)
        ( λ r → le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r) →
      is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q
    backward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ
      q ∃r =
        let
          open do-syntax-trunc-Prop (lower-cut-lim-cauchy-approximation-leq-ℝ q)
        in do
          r , q<r , r<lim ← ∃r
          (ε⁺@(ε , _) , θ⁺@(θ , _)) , r+ε+θ<xε ← r<lim
          let xε = map-cauchy-approximation-leq-ℝ x ε⁺
          intro-exists
            ( ε⁺ , θ⁺)
            ( le-lower-cut-ℝ
              ( xε)
              ( q +ℚ (ε +ℚ θ))
              ( r +ℚ (ε +ℚ θ))
              ( preserves-le-left-add-ℚ (ε +ℚ θ) q r q<r)
              ( r+ε+θ<xε))

    is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q ↔
      exists
        ( ℚ)
        ( λ r → le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r)
    is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ q =
      ( forward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ
          ( q) ,
        backward-implication-is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ
          ( q))

    forward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q →
      exists
        ( ℚ)
        ( λ p → le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p)
    forward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ
      q lim<q =
        let
          open
            do-syntax-trunc-Prop
              ( ∃
                ( ℚ)
                ( λ p →
                  le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p))
        in do
          (ε⁺@(ε , _) , θ⁺@(θ , _)) , xε<q-ε-θ ← lim<q
          let xε = map-cauchy-approximation-leq-ℝ x ε⁺
          p , p<q-ε-θ , xε<p ←
            forward-implication
              ( is-rounded-upper-cut-ℝ xε (q -ℚ (ε +ℚ θ)))
              ( xε<q-ε-θ)
          intro-exists
            ( p +ℚ (ε +ℚ θ))
            ( le-transpose-right-diff-ℚ p q (ε +ℚ θ) p<q-ε-θ ,
              intro-exists
                ( ε⁺ , θ⁺)
                ( inv-tr
                  ( is-in-upper-cut-ℝ xε)
                  ( is-retraction-diff-ℚ (ε +ℚ θ) p)
                  ( xε<p)))

    backward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      exists
        ( ℚ)
        ( λ p → le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p) →
      is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q
    backward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ
      q ∃p =
        let
          open do-syntax-trunc-Prop (upper-cut-lim-cauchy-approximation-leq-ℝ q)
        in do
          p , p<q , lim<p ← ∃p
          (ε⁺@(ε , _) , θ⁺@(θ , _)) , xε<p-ε-θ ← lim<p
          let xε = map-cauchy-approximation-leq-ℝ x ε⁺
          intro-exists
            ( ε⁺ , θ⁺)
            ( le-upper-cut-ℝ
              ( xε)
              ( p -ℚ (ε +ℚ θ))
              ( q -ℚ (ε +ℚ θ))
              ( preserves-le-left-add-ℚ (neg-ℚ (ε +ℚ θ)) p q p<q)
              ( xε<p-ε-θ))

    is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q ↔
      exists
        ( ℚ)
        ( λ p → le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p)
    is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ q =
      ( forward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ
        ( q) ,
        backward-implication-is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ
        ( q))

  lower-real-lim-cauchy-approximation-leq-ℝ : lower-ℝ l
  lower-real-lim-cauchy-approximation-leq-ℝ =
    lower-cut-lim-cauchy-approximation-leq-ℝ ,
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ ,
    is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ

  upper-real-lim-cauchy-approximation-leq-ℝ : upper-ℝ l
  upper-real-lim-cauchy-approximation-leq-ℝ =
    upper-cut-lim-cauchy-approximation-leq-ℝ ,
    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ ,
    is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ

  abstract
    is-disjoint-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      ¬ ( is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q ×
          is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q)
    is-disjoint-cut-lim-cauchy-approximation-leq-ℝ q (q<lim , lim<q) =
      let
        open do-syntax-trunc-Prop empty-Prop
      in do
        (εl⁺@(εl , _) , θl⁺@(θl , _)) , q+εl+θl<xεl ← q<lim
        (εu⁺@(εu , _) , θu⁺@(θu , _)) , xεu<q-εu-θu ← lim<q
        let
          xεl = map-cauchy-approximation-leq-ℝ x εl⁺
          xεu = map-cauchy-approximation-leq-ℝ x εu⁺
          q-εu+θl<xεu : is-in-lower-cut-ℝ xεu ((q -ℚ εu) +ℚ θl)
          q-εu+θl<xεu =
            pr2
              ( is-cauchy-map-cauchy-approximation-leq-ℝ x εl⁺ εu⁺)
              ( (q -ℚ εu) +ℚ θl)
              ( inv-tr
                ( is-in-lower-cut-ℝ xεl)
                ( equational-reasoning
                    ((q -ℚ εu) +ℚ θl) +ℚ (εl +ℚ εu)
                    ＝ ((q +ℚ θl) -ℚ εu) +ℚ (εu +ℚ εl)
                      by
                        ap-add-ℚ
                          ( right-swap-add-ℚ q (neg-ℚ εu) θl)
                          ( commutative-add-ℚ εl εu)
                    ＝ ((q +ℚ θl) -ℚ εu) +ℚ εu +ℚ εl
                      by inv (associative-add-ℚ _ _ _)
                    ＝ (q +ℚ θl) +ℚ εl by ap (_+ℚ εl) (is-section-diff-ℚ _ _)
                    ＝ q +ℚ (θl +ℚ εl) by associative-add-ℚ _ _ _
                    ＝ q +ℚ (εl +ℚ θl) by ap (q +ℚ_) (commutative-add-ℚ _ _))
                ( q+εl+θl<xεl))
        is-disjoint-cut-ℝ
          ( xεu)
          ( q -ℚ εu)
          ( le-lower-cut-ℝ
              ( xεu)
              ( q -ℚ εu)
              ( (q -ℚ εu) +ℚ θl)
              ( le-right-add-rational-ℚ⁺ (q -ℚ εu) θl⁺)
              ( q-εu+θl<xεu) ,
            tr
              ( is-in-upper-cut-ℝ xεu)
              ( equational-reasoning
                (q -ℚ (εu +ℚ θu)) +ℚ θu
                ＝ (q +ℚ (neg-ℚ εu +ℚ neg-ℚ θu)) +ℚ θu
                  by ap (λ r → (q +ℚ r) +ℚ θu) (distributive-neg-add-ℚ εu θu)
                ＝ ((q -ℚ εu) -ℚ θu) +ℚ θu
                  by ap (_+ℚ θu) (inv (associative-add-ℚ _ _ _))
                ＝ q -ℚ εu by is-section-diff-ℚ θu _)
              ( le-upper-cut-ℝ
                ( xεu)
                ( q -ℚ (εu +ℚ θu))
                ( (q -ℚ (εu +ℚ θu)) +ℚ θu)
                ( le-right-add-rational-ℚ⁺ (q -ℚ (εu +ℚ θu)) θu⁺)
                ( xεu<q-εu-θu)))

    is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ :
      is-located-lower-upper-ℝ
        ( lower-real-lim-cauchy-approximation-leq-ℝ)
        ( upper-real-lim-cauchy-approximation-leq-ℝ)
    is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ p q p<q =
      let
        ε'⁺@(ε' , _) , 2ε'⁺<q-p =
          bound-double-le-ℚ⁺ (positive-diff-le-ℚ p q p<q)
        ε⁺@(ε , _) , 2ε⁺<ε'⁺ =
          bound-double-le-ℚ⁺ ε'⁺
        2ε' = ε' +ℚ ε'
        2ε = ε +ℚ ε
        4ε = 2ε +ℚ 2ε
        xε = map-cauchy-approximation-leq-ℝ x ε⁺
      in
        map-disjunction
          ( lower-cut-ℝ xε (p +ℚ 2ε))
          ( lower-cut-lim-cauchy-approximation-leq-ℝ p)
          ( upper-cut-ℝ xε (q -ℚ 2ε))
          ( upper-cut-lim-cauchy-approximation-leq-ℝ q)
          ( intro-exists (ε⁺ , ε⁺))
          ( intro-exists (ε⁺ , ε⁺))
          ( is-located-lower-upper-cut-ℝ
            ( map-cauchy-approximation-leq-ℝ x ε⁺)
            ( p +ℚ 2ε)
            ( q -ℚ 2ε)
            ( le-transpose-left-add-ℚ
              ( p +ℚ 2ε)
              ( 2ε)
              ( q)
              ( inv-tr
                ( λ r → le-ℚ r q)
                ( associative-add-ℚ p 2ε 2ε ∙ commutative-add-ℚ p 4ε)
                ( le-transpose-right-diff-ℚ
                  ( 4ε)
                  ( q)
                  ( p)
                  ( transitive-le-ℚ
                    ( 4ε)
                    ( 2ε')
                    ( q -ℚ p)
                    ( 2ε'⁺<q-p)
                    ( preserves-le-add-ℚ {2ε} {ε'} {2ε} {ε'}
                      ( 2ε⁺<ε'⁺)
                      ( 2ε⁺<ε'⁺)))))))

  lim-cauchy-approximation-leq-ℝ : ℝ l
  lim-cauchy-approximation-leq-ℝ =
    real-lower-upper-ℝ
      ( lower-real-lim-cauchy-approximation-leq-ℝ)
      ( upper-real-lim-cauchy-approximation-leq-ℝ)
      ( is-disjoint-cut-lim-cauchy-approximation-leq-ℝ)
      ( is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ)
```

### The limit satisfies the definition of a limit of a Cauchy approximation

```agda
module _
  {l : Level} (x : cauchy-approximation-leq-ℝ l)
  where

  is-limit-lim-cauchy-approximation-leq-ℝ :
    is-limit-cauchy-approximation-Premetric-Space
      ( premetric-space-leq-ℝ l)
      ( x)
      ( lim-cauchy-approximation-leq-ℝ x)
  is-limit-lim-cauchy-approximation-leq-ℝ ε⁺@(ε , _) θ⁺@(θ , _) =
    let
      open
        do-syntax-trunc-Prop
          ( premetric-leq-ℝ
            ( l)
            ( ε⁺ +ℚ⁺ θ⁺)
            ( map-cauchy-approximation-leq-ℝ x ε⁺)
            ( lim-cauchy-approximation-leq-ℝ x))
      lim = lim-cauchy-approximation-leq-ℝ x
      xε = map-cauchy-approximation-leq-ℝ x ε⁺
      θ'⁺@(θ' , _) = left-summand-split-ℚ⁺ θ⁺
      θ''⁺@(θ'' , _) = right-summand-split-ℚ⁺ θ⁺
      ε+θ'+θ''=ε+θ =
        associative-add-ℚ _ _ _ ∙
        ap (ε +ℚ_) (ap rational-ℚ⁺ (eq-add-split-ℚ⁺ θ⁺))
      ε+θ = real-ℚ (ε +ℚ θ)
      ε+θ' = real-ℚ (ε +ℚ θ')
    in do
      ( r , xε+ε+θ'<r , r<xε+ε+θ) ←
        tr
          ( le-ℝ (xε +ℝ ε+θ'))
          ( associative-add-ℝ _ _ _ ∙
            ap ( xε +ℝ_) (add-real-ℚ _ _ ∙ ap real-ℚ ε+θ'+θ''=ε+θ))
          ( le-left-add-real-ℝ⁺
            ( xε +ℝ ε+θ')
            ( positive-real-ℚ⁺ θ''⁺))
      ( q , xε-ε-θ<q , q<xε-ε-θ') ←
        tr
          ( λ y → le-ℝ y (xε -ℝ ε+θ'))
          ( associative-add-ℝ _ _ _ ∙
            ap
              ( xε +ℝ_)
              ( inv (distributive-neg-add-ℝ _ _) ∙
                ap neg-ℝ (add-real-ℚ _ _ ∙ ap real-ℚ ε+θ'+θ''=ε+θ)))
          ( le-diff-real-ℝ⁺ (xε -ℝ ε+θ') (positive-real-ℚ⁺ θ''⁺))
      neighborhood-leq-dist-ℝ
        ( ε⁺ +ℚ⁺ θ⁺)
        ( xε)
        ( lim)
        ( leq-dist-leq-diff-ℝ
          ( _)
          ( _)
          ( ε+θ)
          ( swap-right-diff-leq-ℝ
            ( xε)
            ( ε+θ)
            ( lim)
            ( leq-le-ℝ
              ( xε -ℝ ε+θ)
              ( lim)
              ( intro-exists
                ( q)
                ( xε-ε-θ<q ,
                  intro-exists
                    ( ε⁺ , θ'⁺)
                    ( transpose-is-in-lower-cut-diff-ℝ
                      ( xε)
                      ( ε +ℚ θ')
                      ( q)
                      ( q<xε-ε-θ'))))))
          ( swap-right-diff-leq-ℝ
            ( lim)
            ( real-ℚ (ε +ℚ θ))
            ( xε)
            ( leq-transpose-right-add-ℝ
              ( lim)
              ( xε)
              ( ε+θ)
              ( leq-le-ℝ
                ( lim)
                ( xε +ℝ ε+θ)
                ( intro-exists
                  ( r)
                  ( intro-exists
                    ( ε⁺ , θ'⁺)
                    ( transpose-is-in-upper-cut-add-ℝ
                      ( xε)
                      ( ε +ℚ θ')
                      ( r)
                      ( xε+ε+θ'<r)) ,
                    r<xε+ε+θ))))))

  is-convergent-cauchy-approximation-leq-ℝ :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-space-leq-ℝ l)
      ( x)
  is-convergent-cauchy-approximation-leq-ℝ =
    ( lim-cauchy-approximation-leq-ℝ x ,
      is-limit-lim-cauchy-approximation-leq-ℝ)
```

### The standard metric space of real numbers is complete

```agda
is-complete-metric-space-leq-ℝ :
  (l : Level) → is-complete-Metric-Space (metric-space-leq-ℝ l)
is-complete-metric-space-leq-ℝ _ = is-convergent-cauchy-approximation-leq-ℝ

complete-metric-space-leq-ℝ :
  (l : Level) → Complete-Metric-Space (lsuc l) l
pr1 (complete-metric-space-leq-ℝ l) = metric-space-leq-ℝ l
pr2 (complete-metric-space-leq-ℝ l) = is-complete-metric-space-leq-ℝ l
```

### Limits of Cauchy sequences in `ℝ`

```agda
cauchy-sequence-ℝ : (l : Level) → UU (lsuc l)
cauchy-sequence-ℝ l =
  cauchy-sequence-Complete-Metric-Space (complete-metric-space-leq-ℝ l)

lim-cauchy-sequence-ℝ : {l : Level} → cauchy-sequence-ℝ l → ℝ l
lim-cauchy-sequence-ℝ {l} =
  limit-cauchy-sequence-Complete-Metric-Space (complete-metric-space-leq-ℝ l)
```
