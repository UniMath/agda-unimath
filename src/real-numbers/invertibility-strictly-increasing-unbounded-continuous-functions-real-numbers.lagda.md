# Invertibility of strictly increasing, unbounded, pointwise continuous functions on ℝ

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.invertibility-strictly-increasing-unbounded-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers

open import order-theory.large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.increasing-functions-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.limits-of-functions-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximations-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-functions-real-numbers
open import real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers
open import real-numbers.unbounded-functions-real-numbers
```

</details>

## Idea

Any
[strictly increasing](real-numbers.strictly-increasing-functions-real-numbers.md),
[pointwise continuous](real-numbers.pointwise-continuous-functions-real-numbers.md),
[unbounded](real-numbers.unbounded-functions-real-numbers.md) function from the
[real numbers](real-numbers.dedekind-real-numbers.md) to themselves is an
[automorphism](foundation.automorphisms.md) of the real numbers. We abbreviate
these conditions as SIPCUB.

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-SIPCUB-prop-function-ℝ : Prop (lsuc l1 ⊔ l2)
  is-SIPCUB-prop-function-ℝ =
    ( is-strictly-increasing-prop-function-ℝ f) ∧
    ( is-pointwise-continuous-prop-function-ℝ f) ∧
    ( is-unbounded-prop-function-ℝ f)

  is-SIPCUB-function-ℝ : UU (lsuc l1 ⊔ l2)
  is-SIPCUB-function-ℝ = type-Prop is-SIPCUB-prop-function-ℝ

SIPCUB-function-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
SIPCUB-function-ℝ l1 l2 = type-subtype (is-SIPCUB-prop-function-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : SIPCUB-function-ℝ l1 l2)
  where

  map-SIPCUB-function-ℝ : ℝ l1 → ℝ l2
  map-SIPCUB-function-ℝ = pr1 f

  abstract
    is-strictly-increasing-SIPCUB-function-ℝ :
      is-strictly-increasing-function-ℝ map-SIPCUB-function-ℝ
    is-strictly-increasing-SIPCUB-function-ℝ = pr1 (pr2 f)

    is-increasing-SIPCUB-function-ℝ :
      is-increasing-function-ℝ map-SIPCUB-function-ℝ
    is-increasing-SIPCUB-function-ℝ =
      is-increasing-is-strictly-increasing-function-ℝ
        ( map-SIPCUB-function-ℝ)
        ( is-strictly-increasing-SIPCUB-function-ℝ)

    is-pointwise-continuous-SIPCUB-function-ℝ :
      is-pointwise-continuous-function-ℝ map-SIPCUB-function-ℝ
    is-pointwise-continuous-SIPCUB-function-ℝ = pr1 (pr2 (pr2 f))

    pointwise-continuous-SIPCUB-function-ℝ :
      pointwise-continuous-function-ℝ l1 l2
    pointwise-continuous-SIPCUB-function-ℝ =
      ( map-SIPCUB-function-ℝ ,
        is-pointwise-continuous-SIPCUB-function-ℝ)

    is-classically-pointwise-continuous-SIPCUB-function-ℝ :
      (x : ℝ l1) →
      is-classical-limit-function-ℝ
        ( map-SIPCUB-function-ℝ)
        ( x)
        ( map-SIPCUB-function-ℝ x)
    is-classically-pointwise-continuous-SIPCUB-function-ℝ =
      is-classically-pointwise-continuous-pointwise-continuous-function-ℝ
        ( pointwise-continuous-SIPCUB-function-ℝ)

    is-unbounded-below-SIPCUB-function-ℝ :
      is-unbounded-below-function-ℝ map-SIPCUB-function-ℝ
    is-unbounded-below-SIPCUB-function-ℝ = pr2 (pr2 (pr2 (pr2 f)))

    is-unbounded-above-SIPCUB-function-ℝ :
      is-unbounded-above-function-ℝ map-SIPCUB-function-ℝ
    is-unbounded-above-SIPCUB-function-ℝ = pr1 (pr2 (pr2 (pr2 f)))

    reflects-le-SIPCUB-function-ℝ :
      (x x' : ℝ l1) →
      le-ℝ (map-SIPCUB-function-ℝ x) (map-SIPCUB-function-ℝ x') →
      le-ℝ x x'
    reflects-le-SIPCUB-function-ℝ =
      reflects-le-is-strictly-increasing-pointwise-continuous-function-ℝ
        ( pointwise-continuous-SIPCUB-function-ℝ)
        ( is-strictly-increasing-SIPCUB-function-ℝ)

    is-injective-SIPCUB-function-ℝ : is-injective map-SIPCUB-function-ℝ
    is-injective-SIPCUB-function-ℝ =
      is-injective-is-strictly-increasing-function-ℝ
        ( map-SIPCUB-function-ℝ)
        ( is-strictly-increasing-SIPCUB-function-ℝ)
```

## Properties

### Any SIPCUB function is invertible

Note we cannot be any more universe-polymorphic.

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  (y : ℝ l)
  where

  lower-cut-inv-SIPCUB-function-ℝ : subtype l ℚ
  lower-cut-inv-SIPCUB-function-ℝ q =
    le-prop-ℝ (map-SIPCUB-function-ℝ f (raise-real-ℚ l q)) y

  upper-cut-inv-SIPCUB-function-ℝ : subtype l ℚ
  upper-cut-inv-SIPCUB-function-ℝ q =
    le-prop-ℝ y (map-SIPCUB-function-ℝ f (raise-real-ℚ l q))

  abstract
    is-inhabited-lower-cut-inv-SIPCUB-function-ℝ :
      is-inhabited-subtype lower-cut-inv-SIPCUB-function-ℝ
    is-inhabited-lower-cut-inv-SIPCUB-function-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop lower-cut-inv-SIPCUB-function-ℝ)
      in do
        (q , q<y) ← is-inhabited-lower-cut-ℝ y
        (x , fx<q) ← is-unbounded-below-SIPCUB-function-ℝ f q
        (p , p<x) ← is-inhabited-lower-cut-ℝ x
        intro-exists
          ( p)
          ( transitive-le-ℝ
            ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
            ( real-ℚ q)
            ( y)
            ( le-real-is-in-lower-cut-ℝ y q<y)
            ( transitive-le-ℝ
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
              ( map-SIPCUB-function-ℝ f x)
              ( real-ℚ q)
              ( fx<q)
              ( is-strictly-increasing-SIPCUB-function-ℝ f _ _
                ( le-raise-real-is-in-lower-cut-ℝ l x p<x))))

    is-inhabited-upper-cut-inv-SIPCUB-function-ℝ :
      is-inhabited-subtype upper-cut-inv-SIPCUB-function-ℝ
    is-inhabited-upper-cut-inv-SIPCUB-function-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop upper-cut-inv-SIPCUB-function-ℝ)
      in do
        (q , y<q) ← is-inhabited-upper-cut-ℝ y
        (x , q<fx) ← is-unbounded-above-SIPCUB-function-ℝ f q
        (p , x<p) ← is-inhabited-upper-cut-ℝ x
        intro-exists
          ( p)
          ( transitive-le-ℝ
            ( y)
            ( real-ℚ q)
            ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
            ( transitive-le-ℝ
              ( real-ℚ q)
              ( map-SIPCUB-function-ℝ f x)
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
              ( is-strictly-increasing-SIPCUB-function-ℝ f _ _
                ( le-raise-real-is-in-upper-cut-ℝ l x x<p))
              ( q<fx))
            ( le-real-is-in-upper-cut-ℝ y y<q))

    forward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-inv-SIPCUB-function-ℝ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-inv-SIPCUB-function-ℝ r)
    forward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ q fq<y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-inv-SIPCUB-function-ℝ r))
      in do
        (ε , fq+ε<y) ← exists-positive-rational-separation-le-ℝ fq<y
        (δ , Hδ) ←
          is-classically-pointwise-continuous-pointwise-continuous-function-ℝ
            ( pointwise-continuous-SIPCUB-function-ℝ f)
            ( raise-real-ℚ l q)
            ( ε)
        intro-exists
          ( q +ℚ rational-ℚ⁺ δ)
          ( le-right-add-rational-ℚ⁺ q δ ,
            concatenate-leq-le-ℝ
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l (q +ℚ rational-ℚ⁺ δ)))
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q) +ℝ real-ℚ⁺ ε)
              ( y)
              ( right-leq-real-bound-neighborhood-ℝ ε
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l (q +ℚ rational-ℚ⁺ δ)))
                ( Hδ
                  ( raise-real-ℚ l (q +ℚ rational-ℚ⁺ δ))
                  ( forward-implication
                    ( is-isometry-metric-space-raise-real-ℚ l
                      ( δ)
                      ( q)
                      ( q +ℚ rational-ℚ⁺ δ))
                    ( neighborhood-add-ℚ q δ))))
              ( fq+ε<y))

    forward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-inv-SIPCUB-function-ℝ q →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-inv-SIPCUB-function-ℝ p)
    forward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ q y<fq =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-inv-SIPCUB-function-ℝ p))
      in do
        (ε , y+ε<fq) ← exists-positive-rational-separation-le-ℝ y<fq
        (δ , Hδ) ←
          is-classically-pointwise-continuous-pointwise-continuous-function-ℝ
            ( pointwise-continuous-SIPCUB-function-ℝ f)
            ( raise-real-ℚ l q)
            ( ε)
        intro-exists
          ( q -ℚ rational-ℚ⁺ δ)
          ( le-diff-rational-ℚ⁺ q δ ,
            concatenate-le-leq-ℝ
              ( y)
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q) -ℝ real-ℚ⁺ ε)
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ)))
              ( le-transpose-left-add-ℝ
                ( y)
                ( real-ℚ⁺ ε)
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                ( y+ε<fq))
              ( leq-transpose-right-add-ℝ
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ)))
                ( real-ℚ⁺ ε)
                ( left-leq-real-bound-neighborhood-ℝ
                  ( ε)
                  ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                  ( map-SIPCUB-function-ℝ
                    ( f)
                    ( raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ)))
                  ( Hδ
                    ( raise-real-ℚ l (q -ℚ rational-ℚ⁺ δ))
                    ( forward-implication
                      ( is-isometry-metric-space-raise-real-ℚ
                        ( l)
                        ( δ)
                        ( q)
                        ( q -ℚ rational-ℚ⁺ δ))
                      ( neighborhood-diff-ℚ q δ))))))

    backward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-inv-SIPCUB-function-ℝ r) →
      is-in-subtype lower-cut-inv-SIPCUB-function-ℝ q
    backward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ q ∃r =
      let
        open do-syntax-trunc-Prop (lower-cut-inv-SIPCUB-function-ℝ q)
      in do
        (r , q<r , fr<y) ← ∃r
        transitive-le-ℝ
          ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
          ( map-SIPCUB-function-ℝ f (raise-real-ℚ l r))
          ( y)
          ( fr<y)
          ( is-strictly-increasing-SIPCUB-function-ℝ f
            ( raise-real-ℚ l q)
            ( raise-ℝ l (real-ℚ r))
            ( le-raise-le-ℝ l (preserves-le-real-ℚ q<r)))

    backward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-inv-SIPCUB-function-ℝ p) →
      is-in-subtype upper-cut-inv-SIPCUB-function-ℝ q
    backward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ q ∃p =
      let
        open do-syntax-trunc-Prop (upper-cut-inv-SIPCUB-function-ℝ q)
      in do
        (p , p<q , y<fp) ← ∃p
        transitive-le-ℝ
          ( y)
          ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
          ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
          ( is-strictly-increasing-SIPCUB-function-ℝ f
            ( raise-real-ℚ l p)
            ( raise-real-ℚ l q)
            ( le-raise-le-ℝ l (preserves-le-real-ℚ p<q)))
          ( y<fp)

    is-rounded-lower-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      ( (is-in-subtype lower-cut-inv-SIPCUB-function-ℝ q) ↔
        (exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-inv-SIPCUB-function-ℝ r)))
    is-rounded-lower-cut-inv-SIPCUB-function-ℝ q =
      ( forward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ q ,
        backward-implication-is-rounded-lower-cut-inv-SIPCUB-function-ℝ q)

    is-rounded-upper-cut-inv-SIPCUB-function-ℝ :
      (q : ℚ) →
      ( (is-in-subtype upper-cut-inv-SIPCUB-function-ℝ q) ↔
        (exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-inv-SIPCUB-function-ℝ p)))
    is-rounded-upper-cut-inv-SIPCUB-function-ℝ q =
      ( forward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ q ,
        backward-implication-is-rounded-upper-cut-inv-SIPCUB-function-ℝ q)

    is-disjoint-lower-upper-cut-inv-SIPCUB-function-ℝ :
      disjoint-subtype
        ( lower-cut-inv-SIPCUB-function-ℝ)
        ( upper-cut-inv-SIPCUB-function-ℝ)
    is-disjoint-lower-upper-cut-inv-SIPCUB-function-ℝ q (fq<y , y<fq) =
      asymmetric-le-ℝ fq<y y<fq

    is-located-lower-upper-cut-inv-SIPCUB-function-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( lower-cut-inv-SIPCUB-function-ℝ p)
        ( upper-cut-inv-SIPCUB-function-ℝ q)
    is-located-lower-upper-cut-inv-SIPCUB-function-ℝ p q p<q =
      cotransitive-le-ℝ
        ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p))
        ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
        ( y)
        ( is-strictly-increasing-SIPCUB-function-ℝ f _ _
          ( le-raise-le-ℝ l (preserves-le-real-ℚ p<q)))

  opaque
    map-inv-SIPCUB-function-ℝ : ℝ l
    map-inv-SIPCUB-function-ℝ =
      real-lower-upper-ℝ
        ( lower-cut-inv-SIPCUB-function-ℝ ,
          is-inhabited-lower-cut-inv-SIPCUB-function-ℝ ,
          is-rounded-lower-cut-inv-SIPCUB-function-ℝ)
        ( upper-cut-inv-SIPCUB-function-ℝ ,
          is-inhabited-upper-cut-inv-SIPCUB-function-ℝ ,
          is-rounded-upper-cut-inv-SIPCUB-function-ℝ)
        ( is-disjoint-lower-upper-cut-inv-SIPCUB-function-ℝ)
        ( is-located-lower-upper-cut-inv-SIPCUB-function-ℝ)
```

## Properties

### The inverse of a SIPCUB function is its retraction

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  (x : ℝ l)
  where

  abstract opaque
    unfolding map-inv-SIPCUB-function-ℝ

    leq-is-retraction-map-inv-SIPCUB-function-ℝ :
      leq-ℝ (map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x)) x
    leq-is-retraction-map-inv-SIPCUB-function-ℝ =
      leq-leq-rational-ℝ _ _
        ( λ q x≤q →
          leq-not-le-ℝ _ _
            ( λ fq<fx →
              not-le-leq-ℝ
                ( map-SIPCUB-function-ℝ f x)
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                ( is-increasing-SIPCUB-function-ℝ f _ _
                  ( preserves-leq-right-raise-ℝ l x≤q))
                ( is-in-lower-cut-le-real-ℚ _ fq<fx)))

    leq-is-retraction-map-inv-SIPCUB-function-ℝ' :
      leq-ℝ x (map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x))
    leq-is-retraction-map-inv-SIPCUB-function-ℝ' =
      leq-leq-rational-ℝ _ _
        ( λ q f⁻¹⟨fx⟩≤q →
          leq-not-le-ℝ _ _
            ( λ q<x →
              not-leq-le-ℝ
                ( real-ℚ q)
                ( map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x))
                ( le-real-is-in-lower-cut-ℝ _
                  ( is-strictly-increasing-SIPCUB-function-ℝ f _ _
                    ( preserves-le-left-raise-ℝ l q<x)))
                ( f⁻¹⟨fx⟩≤q)))

    is-retraction-map-inv-SIPCUB-function-ℝ :
      map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x) ＝ x
    is-retraction-map-inv-SIPCUB-function-ℝ =
      antisymmetric-leq-ℝ _ _
        ( leq-is-retraction-map-inv-SIPCUB-function-ℝ)
        ( leq-is-retraction-map-inv-SIPCUB-function-ℝ')
```

### The inverse of a SIPCUB function is increasing

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  where

  abstract opaque
    unfolding map-inv-SIPCUB-function-ℝ le-ℝ

    is-increasing-map-inv-SIPCUB-function-ℝ :
      (y y' : ℝ l) →
      leq-ℝ y y' →
      leq-ℝ (map-inv-SIPCUB-function-ℝ f y) (map-inv-SIPCUB-function-ℝ f y')
    is-increasing-map-inv-SIPCUB-function-ℝ y y' y≤y' =
      leq-not-le-ℝ _ _
        ( λ f⁻¹y'<f⁻¹y →
          let
            open do-syntax-trunc-Prop empty-Prop
          in do
            (q , y'<fq , fq<y) ← f⁻¹y'<f⁻¹y
            not-le-leq-ℝ
              ( y)
              ( y')
              ( y≤y')
              ( transitive-le-ℝ
                ( y')
                ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                ( y)
                ( fq<y)
                ( y'<fq)))
```

### The inverse of a SIPCUB function is strictly increasing

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  where

  abstract opaque
    unfolding le-ℝ map-inv-SIPCUB-function-ℝ

    is-strictly-increasing-map-inv-SIPCUB-function-ℝ :
      is-strictly-increasing-function-ℝ
        ( map-inv-SIPCUB-function-ℝ f)
    is-strictly-increasing-map-inv-SIPCUB-function-ℝ y y' y<y' =
      let
        x = map-inv-SIPCUB-function-ℝ f y
        x' = map-inv-SIPCUB-function-ℝ f y'
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-inv-SIPCUB-function-ℝ f y)
              ( map-inv-SIPCUB-function-ℝ f y'))
      in do
        (ε , y+ε<y') ←
          exists-positive-rational-separation-le-ℝ {l} {l} {y} {y'} y<y'
        (ε' , 2ε'<ε) ← double-le-ℚ⁺ ε
        (δ , Hδ) ← is-classically-pointwise-continuous-SIPCUB-function-ℝ f x ε'
        (p , fp<y , Nδxp) ← exists-rational-approximation-below-ℝ x δ
        (q , y<fq , Nδxq) ← exists-rational-approximation-above-ℝ x δ
        intro-exists
          ( q)
          ( y<fq ,
            concatenate-leq-le-ℝ
              ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
              ( y +ℝ real-ℚ⁺ ε)
              ( y')
              ( chain-of-inequalities
                map-SIPCUB-function-ℝ f (raise-real-ℚ l q)
                ≤ map-SIPCUB-function-ℝ f x +ℝ real-ℚ⁺ ε'
                  by
                    right-leq-real-bound-neighborhood-ℝ
                      ( ε')
                      ( _)
                      ( _)
                      ( Hδ (raise-real-ℚ l q) Nδxq)
                ≤ ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p) +ℝ real-ℚ⁺ ε') +ℝ
                  ( real-ℚ⁺ ε')
                  by
                    preserves-leq-right-add-ℝ _ _ _
                      ( left-leq-real-bound-neighborhood-ℝ
                        ( ε')
                        ( _)
                        ( _)
                        ( Hδ (raise-real-ℚ l p) Nδxp))
                ≤ ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p)) +ℝ
                  ( real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                  by leq-eq-ℝ (associative-add-ℝ _ _ _)
                ≤ ( map-SIPCUB-function-ℝ f (raise-real-ℚ l p)) +ℝ
                  ( real-ℚ⁺ (ε' +ℚ⁺ ε'))
                  by leq-eq-ℝ (ap-add-ℝ refl (add-real-ℚ _ _))
                ≤ y +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-add-ℝ
                      ( leq-le-ℝ fp<y)
                      ( preserves-leq-real-ℚ (leq-le-ℚ 2ε'<ε)))
              ( y+ε<y'))
```

### The inverse of a SIPCUB function is injective

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  where

  abstract
    is-injective-map-inv-SIPCUB-function-ℝ :
      is-injective (map-inv-SIPCUB-function-ℝ f)
    is-injective-map-inv-SIPCUB-function-ℝ =
      is-injective-is-strictly-increasing-function-ℝ
        ( map-inv-SIPCUB-function-ℝ f)
        ( is-strictly-increasing-map-inv-SIPCUB-function-ℝ f)
```

### The inverse of a SIPCUB function is its section

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  (y : ℝ l)
  where

  abstract
    is-section-map-inv-SIPCUB-function-ℝ :
      map-SIPCUB-function-ℝ f (map-inv-SIPCUB-function-ℝ f y) ＝ y
    is-section-map-inv-SIPCUB-function-ℝ =
      is-injective-map-inv-SIPCUB-function-ℝ
        ( f)
        ( is-retraction-map-inv-SIPCUB-function-ℝ f _)
```

### SIPCUB functions are automorphisms on the real numbers

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  where

  is-equiv-SIPCUB-function-ℝ :
    is-equiv (map-SIPCUB-function-ℝ f)
  is-equiv-SIPCUB-function-ℝ =
    is-equiv-is-invertible
      ( map-inv-SIPCUB-function-ℝ f)
      ( is-section-map-inv-SIPCUB-function-ℝ f)
      ( is-retraction-map-inv-SIPCUB-function-ℝ f)

  aut-SIPCUB-function-ℝ : Aut (ℝ l)
  aut-SIPCUB-function-ℝ =
    ( map-SIPCUB-function-ℝ f , is-equiv-SIPCUB-function-ℝ)
```

### The inverse of a SIPCUB function is unbounded

```agda
module _
  {l : Level}
  (f : SIPCUB-function-ℝ l l)
  where

  abstract
    is-unbounded-above-map-inv-SIPCUB-function-ℝ :
      is-unbounded-above-function-ℝ (map-inv-SIPCUB-function-ℝ f)
    is-unbounded-above-map-inv-SIPCUB-function-ℝ q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l)
              ( λ x → le-prop-ℝ (real-ℚ q) (map-inv-SIPCUB-function-ℝ f x)))
      in do
        (r , fq<r) ←
          is-inhabited-upper-cut-ℝ (map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
        (x , r<fx) ← is-unbounded-above-SIPCUB-function-ℝ f r
        intro-exists
          ( map-SIPCUB-function-ℝ f x)
          ( reflects-le-left-raise-ℝ l
            ( reflects-le-SIPCUB-function-ℝ
              ( f)
              ( raise-real-ℚ l q)
              ( map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x))
              ( inv-tr
                ( le-ℝ _)
                ( is-section-map-inv-SIPCUB-function-ℝ f _)
                ( transitive-le-ℝ
                  ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                  ( real-ℚ r)
                  ( map-SIPCUB-function-ℝ f x)
                  ( r<fx)
                  ( le-real-is-in-upper-cut-ℝ _ fq<r)))))

    is-unbounded-below-map-inv-SIPCUB-function-ℝ :
      is-unbounded-below-function-ℝ (map-inv-SIPCUB-function-ℝ f)
    is-unbounded-below-map-inv-SIPCUB-function-ℝ q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l)
              ( λ x → le-prop-ℝ (map-inv-SIPCUB-function-ℝ f x) (real-ℚ q)))
      in do
        (r , r<fq) ←
          is-inhabited-lower-cut-ℝ (map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
        (x , fx<r) ← is-unbounded-below-SIPCUB-function-ℝ f r
        intro-exists
          ( map-SIPCUB-function-ℝ f x)
          ( reflects-le-right-raise-ℝ l
            ( reflects-le-SIPCUB-function-ℝ
              ( f)
              ( map-inv-SIPCUB-function-ℝ f (map-SIPCUB-function-ℝ f x))
              ( raise-ℝ l (real-ℚ q))
              ( inv-tr
                ( λ z → le-ℝ z (map-SIPCUB-function-ℝ f (raise-real-ℚ l q)))
                ( is-section-map-inv-SIPCUB-function-ℝ f _)
                ( transitive-le-ℝ
                  ( map-SIPCUB-function-ℝ f x)
                  ( real-ℚ r)
                  ( map-SIPCUB-function-ℝ f (raise-real-ℚ l q))
                  ( le-real-is-in-lower-cut-ℝ _ r<fq)
                  ( fx<r)))))
```
