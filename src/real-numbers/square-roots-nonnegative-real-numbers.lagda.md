# Square roots of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.square-roots-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.square-roots-positive-rational-numbers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "square root" WDID=Q134237 WD="square root" Agda=sqrt-ℝ⁰⁺ Disambiguation="of a nonnegative real number"}}
of a [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real number](real-numbers.dedekind-real-numbers.md) `x` is the unique
nonnegative real number `y` such that `y * y = x`.

## Definition

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  lower-cut-sqrt-ℝ⁰⁺ : subtype l ℚ
  lower-cut-sqrt-ℝ⁰⁺ q =
    hom-Prop
      ( is-nonnegative-prop-ℚ q)
      ( lower-cut-ℝ⁰⁺ x (q *ℚ q))

  upper-cut-sqrt-ℝ⁰⁺ : subtype l ℚ
  upper-cut-sqrt-ℝ⁰⁺ q =
    is-positive-prop-ℚ q ∧ upper-cut-ℝ⁰⁺ x (q *ℚ q)

  abstract
    is-inhabited-lower-cut-sqrt-ℝ⁰⁺ : is-inhabited-subtype lower-cut-sqrt-ℝ⁰⁺
    is-inhabited-lower-cut-sqrt-ℝ⁰⁺ =
      intro-exists
        ( neg-one-ℚ)
        ( λ is-nonneg-neg-one-ℚ →
          ex-falso
            ( is-not-negative-and-nonnegativeℚ
              ( is-negative-rational-ℚ⁻ neg-one-ℚ⁻ , is-nonneg-neg-one-ℚ)))

    is-inhabited-upper-cut-sqrt-ℝ⁰⁺ : is-inhabited-subtype upper-cut-sqrt-ℝ⁰⁺
    is-inhabited-upper-cut-sqrt-ℝ⁰⁺ =
      let
        open do-syntax-trunc-Prop (is-inhabited-subtype-Prop upper-cut-sqrt-ℝ⁰⁺)
      in do
        (q⁺@(q , _) , x<q) ← exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ x
        (p⁺@(p , is-pos-p) , q<p²) ← square-le-ℚ⁺' q⁺
        intro-exists
          ( p)
          ( is-pos-p , le-upper-cut-ℝ (real-ℝ⁰⁺ x) q (p *ℚ p) q<p² x<q)

    forward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ :
      (q : ℚ) → is-in-subtype lower-cut-sqrt-ℝ⁰⁺ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-sqrt-ℝ⁰⁺ r)
    forward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ q q²<x =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-sqrt-ℝ⁰⁺ r))
      in
        trichotomy-sign-ℚ q
          ( λ is-neg-q →
            let
              q⁻ = (q , is-neg-q)
            in
              intro-exists
                ( rational-mediant-zero-ℚ⁻ q⁻)
                ( le-mediant-zero-ℚ⁻ q⁻ ,
                  λ is-nonneg-q' →
                    ex-falso
                      ( is-not-negative-and-nonnegativeℚ
                        ( is-negative-rational-ℚ⁻ (mediant-zero-ℚ⁻ q⁻) ,
                          is-nonneg-q'))))
          ( λ q=0 →
            do
              ( q' , 0<q' , q'<x) ←
                forward-implication
                  ( is-rounded-lower-cut-ℝ⁰⁺ x zero-ℚ)
                  ( tr
                    ( is-in-lower-cut-ℝ⁰⁺ x)
                    ( ap-mul-ℚ q=0 q=0 ∙ right-zero-law-mul-ℚ zero-ℚ)
                    ( q²<x
                      ( inv-tr
                        ( is-nonnegative-ℚ)
                        ( q=0)
                        ( is-nonnegative-rational-ℚ⁰⁺ zero-ℚ⁰⁺))))
              let
                is-pos-q' = is-positive-le-zero-ℚ 0<q'
                q'⁺ = (q' , is-pos-q')
              ( p⁺@(p , is-pos-p) , p²<q') ← square-le-ℚ⁺ q'⁺
              intro-exists
                ( p)
                ( inv-tr
                    ( λ r → le-ℚ r p)
                    ( q=0)
                    ( le-zero-is-positive-ℚ is-pos-p) ,
                  λ _ →
                    le-lower-cut-ℝ (real-ℝ⁰⁺ x) (p *ℚ p) q' p²<q' q'<x))
          ( λ is-pos-q →
            do
              (p , q²<p , p<x) ←
                forward-implication
                  ( is-rounded-lower-cut-ℝ⁰⁺ x (q *ℚ q))
                  ( q²<x (is-nonnegative-is-positive-ℚ is-pos-q))
              let
                is-pos-p =
                  is-positive-le-ℚ⁺
                    ( q *ℚ q , is-positive-mul-ℚ is-pos-q is-pos-q)
                    ( p)
                    ( q²<p)
              (q'⁺@(q' , _) , q<q' , q'²<p) ←
                rounded-below-square-le-ℚ⁺ (q , is-pos-q) (p , is-pos-p) q²<p
              intro-exists
                ( q')
                ( q<q' ,
                  λ _ → le-lower-cut-ℝ (real-ℝ⁰⁺ x) (q' *ℚ q') p q'²<p p<x))

    forward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ :
      (r : ℚ) → is-in-subtype upper-cut-sqrt-ℝ⁰⁺ r →
      exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-sqrt-ℝ⁰⁺ q)
    forward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ r (is-pos-r , x<r²) =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-sqrt-ℝ⁰⁺ q))
      in do
        (p , p<r² , x<p) ←
          forward-implication (is-rounded-upper-cut-ℝ⁰⁺ x (r *ℚ r)) x<r²
        let
          is-pos-p = is-positive-is-in-upper-cut-ℝ⁰⁺ x p x<p
        (q⁺@(q , is-pos-q) , q<r , p<q²) ←
          rounded-above-square-le-ℚ⁺ (r , is-pos-r) (p , is-pos-p) p<r²
        intro-exists
          ( q)
          ( q<r , is-pos-q , le-upper-cut-ℝ (real-ℝ⁰⁺ x) p (q *ℚ q) p<q² x<p)

    backward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ :
      (q : ℚ) → exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-sqrt-ℝ⁰⁺ r) →
      is-in-subtype lower-cut-sqrt-ℝ⁰⁺ q
    backward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ q ∃r is-nonneg-q =
      let
        open do-syntax-trunc-Prop (lower-cut-ℝ⁰⁺ x (q *ℚ q))
      in do
        (r , q<r , r<√x) ← ∃r
        let
          is-nonneg-r =
            is-nonnegative-is-positive-ℚ
              ( is-positive-le-ℚ⁰⁺ (q , is-nonneg-q) r q<r)
        le-lower-cut-ℝ
          ( real-ℝ⁰⁺ x)
          ( q *ℚ q)
          ( r *ℚ r)
          ( preserves-le-square-ℚ⁰⁺ (q , is-nonneg-q) (r , is-nonneg-r) q<r)
          ( r<√x is-nonneg-r)

    backward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ :
      (r : ℚ) → exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-sqrt-ℝ⁰⁺ q) →
      is-in-subtype upper-cut-sqrt-ℝ⁰⁺ r
    backward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ r ∃q =
      let open do-syntax-trunc-Prop (upper-cut-sqrt-ℝ⁰⁺ r)
      in do
        (q , q<r , is-pos-q , x<q²) ← ∃q
        let is-pos-r = is-positive-le-ℚ⁺ (q , is-pos-q) r q<r
        ( is-pos-r ,
          le-upper-cut-ℝ
            ( real-ℝ⁰⁺ x)
            ( q *ℚ q)
            ( r *ℚ r)
            ( preserves-le-square-ℚ⁰⁺
              ( q , is-nonnegative-is-positive-ℚ is-pos-q)
              ( r , is-nonnegative-is-positive-ℚ is-pos-r)
              q<r)
            ( x<q²))

    is-rounded-lower-cut-sqrt-ℝ⁰⁺ :
      ( q : ℚ) →
      ( is-in-subtype lower-cut-sqrt-ℝ⁰⁺ q ↔
        exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-sqrt-ℝ⁰⁺ r))
    is-rounded-lower-cut-sqrt-ℝ⁰⁺ q =
      ( forward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ q ,
        backward-implication-is-rounded-lower-cut-sqrt-ℝ⁰⁺ q)

    is-rounded-upper-cut-sqrt-ℝ⁰⁺ :
      ( r : ℚ) →
      ( is-in-subtype upper-cut-sqrt-ℝ⁰⁺ r ↔
        exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-sqrt-ℝ⁰⁺ q))
    is-rounded-upper-cut-sqrt-ℝ⁰⁺ q =
      ( forward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ q ,
        backward-implication-is-rounded-upper-cut-sqrt-ℝ⁰⁺ q)

    is-disjoint-cut-sqrt-ℝ⁰⁺ :
      disjoint-subtype lower-cut-sqrt-ℝ⁰⁺ upper-cut-sqrt-ℝ⁰⁺
    is-disjoint-cut-sqrt-ℝ⁰⁺ q ( q<√x , is-pos-q , x<q²) =
      is-disjoint-cut-ℝ
        ( real-ℝ⁰⁺ x)
        ( q *ℚ q)
        ( q<√x (is-nonnegative-is-positive-ℚ is-pos-q) ,
          x<q²)

    is-located-lower-upper-cut-sqrt-ℝ⁰⁺ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop (lower-cut-sqrt-ℝ⁰⁺ p) (upper-cut-sqrt-ℝ⁰⁺ q)
    is-located-lower-upper-cut-sqrt-ℝ⁰⁺ p q p<q =
      rec-coproduct
        ( λ is-neg-p →
          inl-disjunction
            ( λ is-nonneg-p →
              ex-falso
                ( is-not-negative-and-nonnegativeℚ (is-neg-p , is-nonneg-p))))
        ( λ is-nonneg-p →
          map-disjunction
            ( λ p²<x _ → p²<x)
            ( λ x<q² → (is-positive-le-ℚ⁰⁺ (p , is-nonneg-p) q p<q , x<q²))
            ( is-located-lower-upper-cut-ℝ
              ( real-ℝ⁰⁺ x)
              ( p *ℚ p)
              ( q *ℚ q)
              ( preserves-le-square-ℚ⁰⁺
                ( p , is-nonneg-p)
                ( q , is-nonnegative-le-ℚ⁰⁺ (p , is-nonneg-p) q p<q)
                ( p<q))))
        ( decide-is-negative-is-nonnegative-ℚ p)

  opaque
    real-sqrt-ℝ⁰⁺ : ℝ l
    real-sqrt-ℝ⁰⁺ =
      ( ( lower-cut-sqrt-ℝ⁰⁺ ,
          is-inhabited-lower-cut-sqrt-ℝ⁰⁺ ,
          is-rounded-lower-cut-sqrt-ℝ⁰⁺) ,
        ( upper-cut-sqrt-ℝ⁰⁺ ,
          is-inhabited-upper-cut-sqrt-ℝ⁰⁺ ,
          is-rounded-upper-cut-sqrt-ℝ⁰⁺) ,
        is-disjoint-cut-sqrt-ℝ⁰⁺ ,
        is-located-lower-upper-cut-sqrt-ℝ⁰⁺)
```

## Properties

### The square root of a nonnegative real number is nonnegative

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  opaque
    unfolding real-ℚ real-sqrt-ℝ⁰⁺

    is-nonnegative-real-sqrt-ℝ⁰⁺ : is-nonnegative-ℝ (real-sqrt-ℝ⁰⁺ x)
    is-nonnegative-real-sqrt-ℝ⁰⁺ =
      is-nonnegative-is-positive-upper-cut-ℝ _ (λ _ → pr1)

  sqrt-ℝ⁰⁺ : ℝ⁰⁺ l
  sqrt-ℝ⁰⁺ = (real-sqrt-ℝ⁰⁺ x , is-nonnegative-real-sqrt-ℝ⁰⁺)
```

### The square of the square root of a nonnegative real number is the original number

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  opaque
    unfolding mul-ℝ real-sqrt-ℝ⁰⁺ leq-ℝ leq-ℝ'

    leq-square-sqrt-ℝ⁰⁺ :
      leq-ℝ (square-ℝ (real-sqrt-ℝ⁰⁺ x)) (real-ℝ⁰⁺ x)
    leq-square-sqrt-ℝ⁰⁺ q q<√x² =
      rec-coproduct
        ( leq-negative-lower-cut-is-nonnegative-ℝ
          ( real-ℝ⁰⁺ x)
          ( is-nonnegative-real-ℝ⁰⁺ x)
          ( q))
        ( λ is-nonneg-q →
          let open do-syntax-trunc-Prop (lower-cut-ℝ (real-ℝ⁰⁺ x) q)
          in do
            ( ( ([a,b]@((a , b) , a≤b) , a<√x , √x<b@(is-pos-b , x<b²)) ,
                ([c,d]@((c , d) , c≤d) , c<√x , √x<d@(is-pos-d , x<d²))) ,
              q<[a,b][c,d]) ← q<√x²
            let
              is-pos-xy x y {r} lb1 lb2 =
                is-positive-le-ℚ⁰⁺
                  ( q , is-nonneg-q)
                  ( x *ℚ y)
                  ( concatenate-le-leq-ℚ
                    ( q)
                    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                    ( x *ℚ y)
                    ( q<[a,b][c,d])
                    ( transitive-leq-ℚ _ r _ lb1 lb2))
              is-nonneg-a =
                rec-coproduct
                  ( λ is-neg-a →
                    ex-falso
                      ( is-not-negative-and-positive-ℚ
                        ( is-negative-mul-negative-positive-ℚ
                            ( is-neg-a)
                            ( is-pos-d) ,
                          is-pos-xy
                            ( a)
                            ( d)
                            ( leq-right-min-ℚ _ _)
                            ( leq-left-min-ℚ _ _))))
                  ( id)
                  ( decide-is-negative-is-nonnegative-ℚ a)
              is-nonneg-c =
                rec-coproduct
                  ( λ is-neg-c →
                    ex-falso
                      ( is-not-negative-and-positive-ℚ
                        ( is-negative-mul-positive-negative-ℚ
                            ( is-pos-b)
                            ( is-neg-c) ,
                          is-pos-xy
                            ( b)
                            ( c)
                            ( leq-left-min-ℚ _ _)
                            ( leq-right-min-ℚ _ _))))
                  ( id)
                  ( decide-is-negative-is-nonnegative-ℚ c)
              a' = max-ℚ a c
              a'²<x : is-in-lower-cut-ℝ⁰⁺ x (a' *ℚ a')
              a'²<x =
                rec-coproduct
                  ( λ a≤c →
                    inv-tr
                      ( λ p → is-in-lower-cut-ℝ⁰⁺ x (p *ℚ p))
                      ( left-leq-right-max-ℚ a c a≤c)
                      ( c<√x is-nonneg-c))
                  ( λ c≤a →
                    inv-tr
                      ( λ p → is-in-lower-cut-ℝ⁰⁺ x (p *ℚ p))
                      ( right-leq-left-max-ℚ a c c≤a)
                      ( a<√x is-nonneg-a))
                  ( linear-leq-ℚ a c)
            le-lower-cut-ℝ
              ( real-ℝ⁰⁺ x)
              ( q)
              ( a' *ℚ a')
              ( concatenate-le-leq-ℚ
                ( q)
                ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                ( a' *ℚ a')
                ( q<[a,b][c,d])
                ( pr1
                  ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                    ( [a,b])
                    ( [c,d])
                    ( a')
                    ( a')
                    ( leq-left-max-ℚ a c ,
                      leq-lower-upper-cut-ℝ
                        ( real-sqrt-ℝ⁰⁺ x)
                        ( a')
                        ( b)
                        ( λ _ → a'²<x)
                        ( √x<b))
                    ( leq-right-max-ℚ a c ,
                      leq-lower-upper-cut-ℝ
                        ( real-sqrt-ℝ⁰⁺ x)
                        ( a')
                        ( d)
                        ( λ _ → a'²<x)
                        ( √x<d)))))
              ( a'²<x))
        ( decide-is-negative-is-nonnegative-ℚ q)

    leq-square-sqrt-ℝ⁰⁺' :
      leq-ℝ' (real-ℝ⁰⁺ x) (square-ℝ (real-sqrt-ℝ⁰⁺ x))
    leq-square-sqrt-ℝ⁰⁺' q √x²<q =
      let open do-syntax-trunc-Prop (upper-cut-ℝ⁰⁺ x q)
      in do
        ( ( ([a,b]@((a , b) , a≤b) , a<√x , √x<b@(is-pos-b , x<b²)) ,
            ([c,d]@((c , d) , c≤d) , c<√x , √x<d@(is-pos-d , x<d²))) ,
          [a,b][c,d]<q) ← √x²<q
        let
          b' = min-ℚ b d
          x<b'² =
            rec-coproduct
              ( λ b≤d →
                inv-tr
                  ( λ e → is-in-upper-cut-ℝ⁰⁺ x (e *ℚ e))
                  ( left-leq-right-min-ℚ b d b≤d)
                  ( x<b²))
              ( λ d≤b →
                inv-tr
                  ( λ e → is-in-upper-cut-ℝ⁰⁺ x (e *ℚ e))
                  ( right-leq-left-min-ℚ b d d≤b)
                  ( x<d²))
              ( linear-leq-ℚ b d)
          is-pos-b' =
            rec-coproduct
              ( λ b≤d →
                inv-tr
                  ( is-positive-ℚ)
                  ( left-leq-right-min-ℚ b d b≤d)
                  ( is-pos-b))
              ( λ d≤b →
                inv-tr
                  ( is-positive-ℚ)
                  ( right-leq-left-min-ℚ b d d≤b)
                  ( is-pos-d))
              ( linear-leq-ℚ b d)
          √x<b' = (is-pos-b' , x<b'²)
        le-upper-cut-ℝ
          ( real-ℝ⁰⁺ x)
          ( b' *ℚ b')
          ( q)
          ( concatenate-leq-le-ℚ
            ( b' *ℚ b')
            ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
            ( q)
            ( pr2
              ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
                ( [a,b])
                ( [c,d])
                ( b')
                ( b')
                ( leq-lower-upper-cut-ℝ (real-sqrt-ℝ⁰⁺ x) a b' a<√x √x<b' ,
                  leq-left-min-ℚ b d)
                ( leq-lower-upper-cut-ℝ (real-sqrt-ℝ⁰⁺ x) c b' c<√x √x<b' ,
                  leq-right-min-ℚ b d)))
            ( [a,b][c,d]<q))
          ( x<b'²)

    eq-real-square-sqrt-ℝ⁰⁺ : square-ℝ (real-sqrt-ℝ⁰⁺ x) ＝ real-ℝ⁰⁺ x
    eq-real-square-sqrt-ℝ⁰⁺ =
      antisymmetric-leq-ℝ _ _
        ( leq-square-sqrt-ℝ⁰⁺)
        ( leq-leq'-ℝ
          ( real-ℝ⁰⁺ x)
          ( real-sqrt-ℝ⁰⁺ x *ℝ real-sqrt-ℝ⁰⁺ x)
          ( leq-square-sqrt-ℝ⁰⁺'))
```

### Square roots of nonnegative real numbers are unique

```agda
opaque
  unfolding leq-ℝ leq-ℝ' mul-ℝ sim-ℝ real-sqrt-ℝ⁰⁺

  leq-unique-sqrt-ℝ⁰⁺ :
    {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    sim-ℝ (real-ℝ⁰⁺ y *ℝ real-ℝ⁰⁺ y) (real-ℝ⁰⁺ x) →
    leq-ℝ (real-ℝ⁰⁺ y) (real-sqrt-ℝ⁰⁺ x)
  leq-unique-sqrt-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) (y²≤x , _) q q<y is-nonneg-q =
    let
      open do-syntax-trunc-Prop (lower-cut-ℝ x (q *ℚ q))
    in do
      (r , y<r) ← is-inhabited-upper-cut-ℝ y
      let
        q≤r = leq-lower-upper-cut-ℝ y q r q<y y<r
        [q,r] = ((q , r) , q≤r)
        q⁰⁺ = (q , is-nonneg-q)
        r⁰⁺ = (r , is-nonnegative-leq-ℚ⁰⁺ q⁰⁺ r q≤r)
      y²≤x
        ( q *ℚ q)
        ( leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ
          ( y)
          ( y)
          ( q *ℚ q)
          ( intro-exists
            ( ([q,r] , q<y , y<r) , ([q,r] , q<y , y<r))
            ( leq-min-leq-both-ℚ (q *ℚ q) _ _
            ( leq-min-leq-both-ℚ _ _ _
                ( refl-leq-ℚ _)
                ( preserves-leq-left-mul-ℚ⁰⁺ q⁰⁺ q r q≤r))
              ( leq-min-leq-both-ℚ _ _ _
                ( preserves-leq-right-mul-ℚ⁰⁺ q⁰⁺ q r q≤r)
                ( preserves-leq-mul-ℚ⁰⁺ q⁰⁺ r⁰⁺ q⁰⁺ r⁰⁺ q≤r q≤r)))))

  leq-unique-sqrt-ℝ⁰⁺' :
    {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    sim-ℝ (real-ℝ⁰⁺ y *ℝ real-ℝ⁰⁺ y) (real-ℝ⁰⁺ x) →
    leq-ℝ' (real-sqrt-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)
  leq-unique-sqrt-ℝ⁰⁺' x⁰⁺@(x , _) y⁰⁺@(y , is-nonneg-y) (_ , x≤y²) q y<q =
    let
      is-pos-q = is-positive-is-in-upper-cut-ℝ⁰⁺ y⁰⁺ q y<q
      q⁺ = (q , is-pos-q)
      p⁻@(p , is-neg-p) = neg-ℚ⁺ q⁺
      p≤q = leq-negative-positive-ℚ p⁻ q⁺
      [p,q] = ((p , q) , p≤q)
      p<y = leq-negative-lower-cut-is-nonnegative-ℝ y is-nonneg-y p is-neg-p
    in
      ( is-pos-q ,
        leq'-leq-ℝ
          ( x)
          ( y *ℝ y)
          ( x≤y²)
          ( q *ℚ q)
          ( leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ
            ( y)
            ( y)
            ( q *ℚ q)
            ( intro-exists
              ( ([p,q] , p<y , y<q) , ([p,q] , p<y , y<q))
              ( leq-max-leq-both-ℚ _ _ _
                ( leq-max-leq-both-ℚ _ _ _
                  ( leq-eq-ℚ _ _ (negative-law-mul-ℚ q q))
                  ( leq-negative-positive-ℚ
                    ( mul-negative-positive-ℚ p⁻ q⁺)
                    ( q⁺ *ℚ⁺ q⁺)))
                ( leq-max-leq-both-ℚ _ _ _
                  ( leq-negative-positive-ℚ
                    ( mul-positive-negative-ℚ q⁺ p⁻)
                    ( q⁺ *ℚ⁺ q⁺))
                  ( refl-leq-ℚ _))))))

  unique-sqrt-ℝ⁰⁺ : {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    sim-ℝ (real-ℝ⁰⁺ y *ℝ real-ℝ⁰⁺ y) (real-ℝ⁰⁺ x) →
    sim-ℝ (real-ℝ⁰⁺ y) (real-sqrt-ℝ⁰⁺ x)
  unique-sqrt-ℝ⁰⁺ x y y²=x =
    ( leq-unique-sqrt-ℝ⁰⁺ x y y²=x ,
      leq-leq'-ℝ (real-sqrt-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (leq-unique-sqrt-ℝ⁰⁺' x y y²=x))
```

### Squaring is an automorphism on the nonnegative real numbers

```agda
abstract
  is-section-square-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → square-ℝ⁰⁺ (sqrt-ℝ⁰⁺ x) ＝ x
  is-section-square-ℝ⁰⁺ x =
    eq-ℝ⁰⁺ (square-ℝ⁰⁺ (sqrt-ℝ⁰⁺ x)) x (eq-real-square-sqrt-ℝ⁰⁺ x)

  is-retraction-square-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → sqrt-ℝ⁰⁺ (square-ℝ⁰⁺ x) ＝ x
  is-retraction-square-ℝ⁰⁺ x =
    eq-ℝ⁰⁺
      ( sqrt-ℝ⁰⁺ (square-ℝ⁰⁺ x))
      ( x)
      ( inv (eq-sim-ℝ (unique-sqrt-ℝ⁰⁺ (square-ℝ⁰⁺ x) x (refl-sim-ℝ _))))

is-equiv-square-ℝ⁰⁺ : (l : Level) → is-equiv (square-ℝ⁰⁺ {l})
is-equiv-square-ℝ⁰⁺ l =
  is-equiv-is-invertible
    ( sqrt-ℝ⁰⁺)
    ( is-section-square-ℝ⁰⁺)
    ( is-retraction-square-ℝ⁰⁺)

equiv-square-ℝ⁰⁺ : (l : Level) → Aut (ℝ⁰⁺ l)
equiv-square-ℝ⁰⁺ l = (square-ℝ⁰⁺ , is-equiv-square-ℝ⁰⁺ l)
```

### If `p² = q` for rational `p` and `q`, then the square root of `q` as a real number is `p` as a real number

```agda
abstract
  sqrt-real-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q : ℚ⁰⁺) → (p *ℚ⁰⁺ p ＝ q) →
    sqrt-ℝ⁰⁺ (nonnegative-real-ℚ⁰⁺ q) ＝ nonnegative-real-ℚ⁰⁺ p
  sqrt-real-ℚ⁰⁺ p⁰⁺@(p , _) q⁰⁺@(q , _) p²=q =
    eq-ℝ⁰⁺ _ _
      ( inv
        ( eq-sim-ℝ
          ( unique-sqrt-ℝ⁰⁺
            ( nonnegative-real-ℚ⁰⁺ q⁰⁺)
            ( nonnegative-real-ℚ⁰⁺ p⁰⁺)
            ( sim-eq-ℝ
              ( mul-real-ℚ p p ∙ ap real-ℚ (ap rational-ℚ⁰⁺ p²=q))))))
```

### The square root operation preserves similarity

```agda
abstract
  preserves-sim-sqrt-ℝ⁰⁺ :
    {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → sim-ℝ⁰⁺ x y →
    sim-ℝ⁰⁺ (sqrt-ℝ⁰⁺ x) (sqrt-ℝ⁰⁺ y)
  preserves-sim-sqrt-ℝ⁰⁺ x y x~y =
    unique-sqrt-ℝ⁰⁺
      ( y)
      ( sqrt-ℝ⁰⁺ x)
      ( similarity-reasoning-ℝ
        real-sqrt-ℝ⁰⁺ x *ℝ real-sqrt-ℝ⁰⁺ x
        ~ℝ real-ℝ⁰⁺ x by sim-eq-ℝ (eq-real-square-sqrt-ℝ⁰⁺ x)
        ~ℝ real-ℝ⁰⁺ y by x~y)
```

### The square root operation distributes over multiplication of nonnegative real numbers

```agda
abstract
  distributive-sqrt-mul-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    sqrt-ℝ⁰⁺ (x *ℝ⁰⁺ y) ＝ sqrt-ℝ⁰⁺ x *ℝ⁰⁺ sqrt-ℝ⁰⁺ y
  distributive-sqrt-mul-ℝ⁰⁺ x y =
    eq-ℝ⁰⁺
      ( sqrt-ℝ⁰⁺ (x *ℝ⁰⁺ y))
      ( sqrt-ℝ⁰⁺ x *ℝ⁰⁺ sqrt-ℝ⁰⁺ y)
      ( inv
        ( eq-sim-ℝ
          ( unique-sqrt-ℝ⁰⁺
            ( x *ℝ⁰⁺ y)
            ( sqrt-ℝ⁰⁺ x *ℝ⁰⁺ sqrt-ℝ⁰⁺ y)
            ( sim-eq-ℝ
              ( equational-reasoning
                square-ℝ (real-sqrt-ℝ⁰⁺ x *ℝ real-sqrt-ℝ⁰⁺ y)
                ＝ square-ℝ (real-sqrt-ℝ⁰⁺ x) *ℝ square-ℝ (real-sqrt-ℝ⁰⁺ y)
                  by distributive-square-mul-ℝ _ _
                ＝ real-ℝ⁰⁺ (x *ℝ⁰⁺ y)
                  by
                    ap
                      ( real-ℝ⁰⁺)
                      ( ap-mul-ℝ⁰⁺
                        ( is-section-square-ℝ⁰⁺ x)
                        ( is-section-square-ℝ⁰⁺ y)))))))
```
