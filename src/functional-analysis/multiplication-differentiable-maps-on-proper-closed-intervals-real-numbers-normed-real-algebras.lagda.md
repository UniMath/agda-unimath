# Multiplication of differentiable maps from proper closed intervals in the real numbers to normed real algebras

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.multiplication-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras
open import functional-analysis.uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import group-theory.abelian-groups

open import linear-algebra.normed-real-algebras

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Given two
[differentiable](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras.md)
maps `f` and `g` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real algebra](linear-algebra.normed-real-algebras.md) `A`, the product
map `x ↦ f x * g x` is differentiable with derivative
`x ↦ f' x * g x + f x * g' x`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let nvs-A = normed-vector-space-Normed-ℝ-Algebra A)
  (let _*A_ = mul-Normed-ℝ-Algebra A)
  (let _ℝ*A_ = scalar-mul-Normed-ℝ-Algebra A)
  (let _+A_ = add-Normed-ℝ-Algebra A)
  (let _-A_ = diff-Normed-ℝ-Algebra A)
  (let neg-A = neg-Normed-ℝ-Algebra A)
  (let dist-A = dist-Normed-ℝ-Algebra A)
  (let dist-A⁰⁺ = nonnegative-dist-Normed-ℝ-Algebra A)
  (let norm-A = map-norm-Normed-ℝ-Algebra A)
  (let norm-A⁰⁺ = nonnegative-norm-Normed-ℝ-Algebra A)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  ((f , f' , Df) (g , g' , Dg) :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra A [a,b])
  where

  map-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A
  map-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra x =
    f x *A g x

  map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A
  map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
    x =
    (f' x *A g x) +A (f x *A g' x)

  abstract
    lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
      (x y : type-proper-closed-interval-ℝ l1 [a,b]) (z : ℝ l1) →
      dist-A
        ( (f y *A g y) -A (f x *A g x))
        ( z ℝ*A ((f' x *A g x) +A (f x *A g' x))) ＝
      norm-A
        ( ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x))) +A
          ( ((f y -A f x) -A (z ℝ*A f' x)) *A g x))
    lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
      x y z =
      equational-reasoning
        dist-A
          ( (f y *A g y) -A (f x *A g x))
          ( z ℝ*A ((f' x *A g x) +A (f x *A g' x)))
        ＝ dist-A
            ( (f y *A g y) -A (f x *A g x))
            ( (z ℝ*A (f' x *A g x)) +A (z ℝ*A (f x *A g' x)))
          by
            ap-binary
              ( dist-A)
              ( refl)
              ( left-distributive-scalar-mul-add-Normed-ℝ-Algebra A _ _ _)
        ＝ dist-A
            ( (f y *A g y) -A (f x *A g x))
            ( (z ℝ*A (f x *A g' x)) +A (z ℝ*A (f' x *A g x)))
          by
            ap-binary
              ( dist-A)
              ( refl)
              ( commutative-add-Normed-ℝ-Algebra A _ _)
        ＝ norm-A
            ( ((f y *A g y) -A (z ℝ*A (f x *A g' x))) +A
              ( neg-A (f x *A g x) -A (z ℝ*A (f' x *A g x))))
          by ap norm-A (interchange-add-diff-Normed-ℝ-Algebra A _ _ _ _)
        ＝ dist-A
            ( (f y *A g y) -A (f x *A (z ℝ*A g' x)))
            ( (f x *A g x) +A (z ℝ*A (f' x *A g x)))
          by
            ap
              ( norm-A)
              ( ap-binary
                ( _+A_)
                ( ap-binary
                  ( _-A_)
                  ( refl)
                  ( left-swap-scalar-mul-mul-Normed-ℝ-Algebra A _ _ _))
                ( inv (distributive-neg-add-Normed-ℝ-Algebra A _ _)))
        ＝ dist-A
            ( ((f y *A g y) -A (f x *A (z ℝ*A g' x))) -A (f y *A g x))
            ( ((f x *A g x) +A (z ℝ*A (f' x *A g x))) -A (f y *A g x))
          by inv (dist-right-add-Normed-ℝ-Algebra A _ _ _)
        ＝ dist-A
            ( ((f y *A g y) -A (f x *A (z ℝ*A g' x))) -A (f y *A g x))
            ( ((f x *A g x) +A ((z ℝ*A f' x) *A g x)) -A (f y *A g x))
          by
            ap-binary
              ( dist-A)
              ( refl)
              ( ap-binary
                ( _-A_)
                ( ap-binary
                  ( _+A_)
                  ( refl)
                  ( inv (associative-scalar-mul-mul-Normed-ℝ-Algebra A _ _ _)))
                ( refl))
        ＝ dist-A
            ( ((f y *A g y) -A (f y *A g x)) -A (f x *A (z ℝ*A g' x)))
            ( ((f x *A g x) -A (f y *A g x)) +A ((z ℝ*A f' x) *A g x))
          by
            ap-binary
              ( dist-A)
              ( right-swap-add-Normed-ℝ-Algebra A _ _ _)
              ( right-swap-add-Normed-ℝ-Algebra A _ _ _)
        ＝ dist-A
            ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x)))
            ( ((f x -A f y) *A g x) +A ((z ℝ*A f' x) *A g x))
          by
            ap-binary
              ( dist-A)
              ( ap-binary
                ( _-A_)
                ( inv (left-distributive-mul-diff-Normed-ℝ-Algebra A _ _ _))
                ( refl))
              ( ap-binary
                ( _+A_)
                ( inv (right-distributive-mul-diff-Normed-ℝ-Algebra A _ _ _))
                ( refl))
        ＝ dist-A
            ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x)))
            ( ((f x -A f y) +A (z ℝ*A f' x)) *A g x)
          by
            ap-binary
              ( dist-A)
              ( refl)
              ( inv (right-distributive-mul-add-Normed-ℝ-Algebra A _ _ _))
        ＝ norm-A
            ( ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x))) +A
              ( neg-A ((f x -A f y) +A (z ℝ*A f' x)) *A g x))
          by
            ap
              ( norm-A)
              ( ap-binary
                ( _+A_)
                ( refl)
                ( inv (left-negative-law-mul-Normed-ℝ-Algebra A _ _)))
        ＝ norm-A
            ( ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x))) +A
              ( (neg-A (f x -A f y) -A (z ℝ*A f' x)) *A g x))
          by
            ap
              ( norm-A)
              ( ap-binary
                ( _+A_)
                ( refl)
                ( ap-binary
                  ( _*A_)
                  ( distributive-neg-add-Normed-ℝ-Algebra A _ _)
                  ( refl)))
        ＝ norm-A
            ( ( (f y *A (g y -A g x)) -A (f x *A (z ℝ*A g' x))) +A
              ( ((f y -A f x) -A (z ℝ*A f' x)) *A g x))
          by
            ap
              ( norm-A)
              ( ap-binary
                ( _+A_)
                ( refl)
                ( ap-binary
                  ( _*A_)
                  ( ap-binary
                    ( _-A_)
                    ( neg-diff-Normed-ℝ-Algebra A _ _)
                    ( refl))
                  ( refl)))

    lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra' :
      (c : ℝ l1) (M ε : ℚ⁺) →
      let
        ε' = inv-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M) *ℚ⁺ ε
      in
        (real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c)) +ℝ
        (real-ℚ⁺ ε' *ℝ (c *ℝ real-ℚ⁺ M)) +ℝ
        (real-ℚ⁺ ε' *ℝ c *ℝ real-ℚ⁺ M) ＝
        real-ℚ⁺ ε *ℝ c
    lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra'
      c M ε =
      let
        ε' = inv-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M) *ℚ⁺ ε
      in
      equational-reasoning
        (real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c)) +ℝ
        (real-ℚ⁺ ε' *ℝ (c *ℝ real-ℚ⁺ M)) +ℝ
        (real-ℚ⁺ ε' *ℝ c *ℝ real-ℚ⁺ M)
        ＝
          real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c) +ℝ
          real-ℚ⁺ ε' *ℝ (real-ℚ⁺ M *ℝ c) +ℝ
          real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c)
          by
            ap-add-ℝ
              ( ap-add-ℝ refl (ap-mul-ℝ refl (commutative-mul-ℝ _ _)))
              ( commutative-mul-ℝ _ _)
        ＝
          real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c) +ℝ
          real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c) +ℝ
          real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c)
          by ap-add-ℝ (ap-add-ℝ refl (left-swap-mul-ℝ _ _ _)) refl
        ＝ real-ℕ 3 *ℝ (real-ℚ⁺ M *ℝ (real-ℚ⁺ ε' *ℝ c))
          by inv (left-mul-real-ℕ 3 _)
        ＝ real-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M) *ℝ (real-ℚ⁺ ε' *ℝ c)
          by combine-left-mul-real-ℚ _ _ _
        ＝ real-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M *ℚ⁺ ε') *ℝ c
          by combine-left-mul-real-ℚ _ _ _
        ＝ real-ℚ⁺ ε *ℝ c
          by
            ap-mul-ℝ
              ( ap real-ℚ (is-section-left-div-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M) _))
              ( refl)

    is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
      is-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra
        ( A)
        ( [a,b])
        ( map-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
        ( map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
    is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra
              ( A)
              ( [a,b])
              ( map-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
              ( map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        ((Mf , _) , is-bound-Mf) =
          nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( nvs-A)
            ( [a,b])
            ( uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
              ( A)
              ( [a,b])
              ( f , f' , Df))
        ((Mg , _) , is-bound-Mg) =
          nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( nvs-A)
            ( [a,b])
            ( uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
              ( A)
              ( [a,b])
              ( g , g' , Dg))
        ((Mg' , _) , is-bound-Mg') =
          nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( nvs-A)
            ( [a,b])
            ( uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
              ( A)
              ( [a,b])
              ( g , g' , Dg))
        M₀ = max-ℝ (max-ℝ Mf Mg) Mg'
      in do
        (δf , is-mod-δf) ← Df
        (δg , is-mod-δg) ← Dg
        (ωf , is-mod-ωf) ←
          is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
            ( A)
            ( [a,b])
            ( f , f' , Df)
        (M , M₀<M) ← exists-greater-positive-rational-ℝ M₀
        let
          min-δ ε = min-ℚ⁺ (min-ℚ⁺ (δf ε) (δg ε)) (ωf ε)
          shrink ε = inv-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M) *ℚ⁺ ε
          δ ε = min-δ (shrink ε)
          |f|≤M x =
            chain-of-inequalities
              norm-A (f x)
              ≤ Mf
                by is-bound-Mf x
              ≤ max-ℝ Mf Mg
                by leq-left-max-ℝ Mf Mg
              ≤ M₀
                by leq-left-max-ℝ _ Mg'
              ≤ real-ℚ⁺ M
                by leq-le-ℝ M₀<M
          |g|≤M x =
            chain-of-inequalities
              norm-A (g x)
              ≤ Mg
                by is-bound-Mg x
              ≤ max-ℝ Mf Mg
                by leq-right-max-ℝ Mf Mg
              ≤ M₀
                by leq-left-max-ℝ _ Mg'
              ≤ real-ℚ⁺ M
                by leq-le-ℝ M₀<M
          |g'|≤M x =
            chain-of-inequalities
              norm-A (g' x)
              ≤ Mg'
                by is-bound-Mg' x
              ≤ M₀
                by leq-right-max-ℝ _ Mg'
              ≤ real-ℚ⁺ M
                by leq-le-ℝ M₀<M
          δ≤δf-shrink ε =
            transitive-leq-ℚ⁺
              ( δ ε)
              ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( δf (shrink ε))
              ( leq-left-min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( leq-left-min-ℚ⁺
                ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
                ( ωf (shrink ε)))
          δ≤δg-shrink ε =
            transitive-leq-ℚ⁺
              ( δ ε)
              ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( δg (shrink ε))
              ( leq-right-min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( leq-left-min-ℚ⁺
                ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
                ( ωf (shrink ε)))
          δ≤ωf-shrink ε =
            leq-right-min-ℚ⁺
              ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( ωf (shrink ε))
          is-mod-δ ε x y Nδxy =
            chain-of-inequalities
              dist-A
                ( (f y *A g y) -A (f x *A g x))
                ( (pr1 y -ℝ pr1 x) ℝ*A ((f' x *A g x) +A (f x *A g' x)))
              ≤ norm-A
                  ( ( (f y *A (g y -A g x)) -A
                      (f x *A ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +A
                    ( ((f y -A f x) -A ((pr1 y -ℝ pr1 x) ℝ*A f' x)) *A g x))
                by
                  leq-eq-ℝ
                    ( lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
                      ( x)
                      ( y)
                      ( pr1 y -ℝ pr1 x))
              ≤ ( dist-A
                  ( f y *A (g y -A g x))
                  ( f x *A ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( norm-A (((f y -A f x) -A ((pr1 y -ℝ pr1 x) ℝ*A f' x)) *A g x))
                by triangular-norm-Normed-ℝ-Algebra A _ _
              ≤ ( dist-A
                  ( f y *A (g y -A g x))
                  ( f y *A ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( dist-A
                  ( f y *A ((pr1 y -ℝ pr1 x) ℝ*A g' x))
                  ( f x *A ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( ( dist-A (f y -A f x) ((pr1 y -ℝ pr1 x) ℝ*A f' x)) *ℝ
                  ( map-norm-Normed-ℝ-Algebra A (g x)))
                by
                  preserves-leq-add-ℝ
                    ( triangular-dist-Normed-ℝ-Algebra A _ _ _)
                    ( is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)
              ≤ ( ( map-norm-Normed-ℝ-Algebra A (f y)) *ℝ
                  ( dist-A (g y -A g x) ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( ( dist-A (f y) (f x)) *ℝ
                  ( map-norm-Normed-ℝ-Algebra A ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( ( dist-A (f y -A f x) ((pr1 y -ℝ pr1 x) ℝ*A f' x)) *ℝ
                  ( map-norm-Normed-ℝ-Algebra A (g x)))
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( preserves-leq-add-ℝ
                      ( leq-dist-left-mul-Normed-ℝ-Algebra A _ _ _)
                      ( leq-dist-right-mul-Normed-ℝ-Algebra A _ _ _))
              ≤ ( ( norm-A (f y)) *ℝ
                  ( dist-A (g y -A g x) ((pr1 y -ℝ pr1 x) ℝ*A g' x))) +ℝ
                ( ( dist-A (f y) (f x)) *ℝ
                  ( ( dist-ℝ (pr1 y) (pr1 x)) *ℝ norm-A (g' x))) +ℝ
                ( ( dist-A (f y -A f x) ((pr1 y -ℝ pr1 x) ℝ*A f' x)) *ℝ
                  ( norm-A (g x)))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ
                        ( refl)
                        ( ap-mul-ℝ
                          ( refl)
                          ( is-absolutely-homogeneous-norm-Normed-ℝ-Algebra A
                            ( _)
                            ( _))))
                      ( refl))
              ≤ (real-ℚ⁺ M *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ (pr1 y) (pr1 x))) +ℝ
                (real-ℚ⁺ (shrink ε) *ℝ (dist-ℝ (pr1 y) (pr1 x) *ℝ real-ℚ⁺ M)) +ℝ
                (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ (pr1 y) (pr1 x) *ℝ real-ℚ⁺ M)
                by
                  preserves-leq-add-ℝ
                    ( preserves-leq-add-ℝ
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( norm-A⁰⁺ (f y))
                        ( nonnegative-real-ℚ⁺ M)
                        ( dist-A⁰⁺ _ _)
                        ( nonnegative-real-ℚ⁺ (shrink ε) *ℝ⁰⁺
                          nonnegative-dist-ℝ (pr1 y) (pr1 x))
                        ( |f|≤M y)
                        ( is-mod-δg
                          ( shrink ε)
                          ( x)
                          ( y)
                          ( weakly-monotonic-neighborhood-ℝ
                            ( pr1 x)
                            ( pr1 y)
                            ( δ ε)
                            ( δg (shrink ε))
                            ( δ≤δg-shrink ε)
                            ( Nδxy))))
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( dist-A⁰⁺ (f y) (f x))
                        ( nonnegative-real-ℚ⁺ (shrink ε))
                        ( nonnegative-dist-ℝ (pr1 y) (pr1 x) *ℝ⁰⁺
                          norm-A⁰⁺ (g' x))
                        ( nonnegative-dist-ℝ (pr1 y) (pr1 x) *ℝ⁰⁺
                          nonnegative-real-ℚ⁺ M)
                        ( is-mod-ωf
                          ( y)
                          ( shrink ε)
                          ( x)
                          ( weakly-monotonic-neighborhood-ℝ
                            ( pr1 y)
                            ( pr1 x)
                            ( δ ε)
                            ( ωf (shrink ε))
                            ( δ≤ωf-shrink ε)
                            ( is-symmetric-neighborhood-ℝ _ _ _ Nδxy)))
                        ( preserves-leq-left-mul-ℝ⁰⁺
                          ( nonnegative-dist-ℝ (pr1 y) (pr1 x))
                          ( |g'|≤M x))))
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( dist-A⁰⁺ _ _)
                      ( nonnegative-real-ℚ⁺ (shrink ε) *ℝ⁰⁺
                        nonnegative-dist-ℝ (pr1 y) (pr1 x))
                      ( norm-A⁰⁺ (g x))
                      ( nonnegative-real-ℚ⁺ M)
                      ( is-mod-δf
                        ( shrink ε)
                        ( x)
                        ( y)
                        ( weakly-monotonic-neighborhood-ℝ
                          ( pr1 x)
                          ( pr1 y)
                          ( δ ε)
                          ( δf (shrink ε))
                          ( δ≤δf-shrink ε)
                          ( Nδxy)))
                      ( |g|≤M x))
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 y) (pr1 x)
                by
                  leq-eq-ℝ
                    ( lemma-is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra'
                      ( dist-ℝ (pr1 y) (pr1 x))
                      ( M)
                      ( ε))
        intro-exists
          ( δ)
          ( is-mod-δ)

  mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
      ( A)
      ( [a,b])
  mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    ( map-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra ,
      map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra ,
      is-derivative-map-derivative-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
```
