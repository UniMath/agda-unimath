# Differentiable real functions on proper closed intervals of ℝ

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.differentiable-real-functions-on-proper-closed-intervals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import lists.sequences

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.accumulation-points-subsets-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Given a function `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` of [real numbers](real-numbers.dedekind-real-numbers.md) to the real
numbers, `g` is a
{{#concept "derivative" Disambiguation="of a real-valued function on a proper closed interval" WD="derivative" WDID=Q29175 Agda=is-derivative-real-function-proper-closed-interval-ℝ}}
of `f` if there [exists](foundation.existential-quantification.md) a modulus
function `μ` such that for `ε : ℚ⁺` and any `x` and `y` in `[a, b]` within a
`μ(ε)`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, we have $$|f(y) - f(x) - g(x)(y - x)| ≤ ε|y - x|.$$

## Definition

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  where

  is-modulus-of-derivative-prop-real-function-proper-closed-interval-ℝ :
    (ℚ⁺ → ℚ⁺) → Prop (lsuc l1 ⊔ l2)
  is-modulus-of-derivative-prop-real-function-proper-closed-interval-ℝ μ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( λ (x , x∈[a,b]) →
            Π-Prop
              ( type-proper-closed-interval-ℝ l1 [a,b])
              ( λ (y , y∈[a,b]) →
                hom-Prop
                  ( neighborhood-prop-ℝ l1 (μ ε) x y)
                  ( leq-prop-ℝ
                    ( dist-ℝ
                      ( f (y , y∈[a,b]) -ℝ f (x , x∈[a,b]))
                      ( g (x , x∈[a,b]) *ℝ (y -ℝ x)))
                    ( real-ℚ⁺ ε *ℝ dist-ℝ x y)))))

  is-modulus-of-derivative-real-function-proper-closed-interval-ℝ :
    (ℚ⁺ → ℚ⁺) → UU (lsuc l1 ⊔ l2)
  is-modulus-of-derivative-real-function-proper-closed-interval-ℝ =
    is-in-subtype
      ( is-modulus-of-derivative-prop-real-function-proper-closed-interval-ℝ)

  is-derivative-prop-real-function-proper-closed-interval-ℝ :
    Prop (lsuc l1 ⊔ l2)
  is-derivative-prop-real-function-proper-closed-interval-ℝ =
    is-inhabited-subtype-Prop
      ( is-modulus-of-derivative-prop-real-function-proper-closed-interval-ℝ)

  is-derivative-real-function-proper-closed-interval-ℝ : UU (lsuc l1 ⊔ l2)
  is-derivative-real-function-proper-closed-interval-ℝ =
    type-Prop is-derivative-prop-real-function-proper-closed-interval-ℝ
```

## Properties

### Proving the derivative of a function from a modulus

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  where

  is-derivative-modulus-of-real-function-proper-closed-interval-ℝ :
    ( (ε : ℚ⁺) →
      Σ ( ℚ⁺)
        ( λ δ →
          (x y : type-proper-closed-interval-ℝ l1 [a,b]) →
          neighborhood-ℝ l1 δ (pr1 x) (pr1 y) →
          leq-ℝ
            ( dist-ℝ (f y -ℝ f x) (g x *ℝ (pr1 y -ℝ pr1 x)))
            ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)))) →
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g
  is-derivative-modulus-of-real-function-proper-closed-interval-ℝ μ =
    intro-exists (pr1 ∘ μ) (pr2 ∘ μ)
```

### If `g` is a derivative of `f`, and `aₙ` is a sequence accumulating to `x`, and the limit exists, then `g x` is equal to the limit of `(f aₙ - f x)/(aₙ - x)` as `n → ∞`

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (x : type-proper-closed-interval-ℝ l1 [a,b])
  (y :
    sequence-accumulating-to-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( pr1 x))
  where

  sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ :
    sequence (ℝ (l1 ⊔ l2))
  sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ n =
    (f (pr1 y n) -ℝ f x) *ℝ
    real-inv-nonzero-ℝ
      ( nonzero-diff-apart-ℝ
        ( real-sequence-accumulating-to-point-subset-ℝ
          ( subtype-proper-closed-interval-ℝ l1 [a,b])
          ( pr1 x)
          ( y)
          ( n))
        ( pr1 x)
        ( apart-sequence-accumulating-to-point-subset-ℝ
          ( subtype-proper-closed-interval-ℝ l1 [a,b])
          ( pr1 x)
          ( y)
          ( n)))

module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (x : type-proper-closed-interval-ℝ l1 [a,b])
  (y :
    sequence-accumulating-to-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( pr1 x))
  where

  abstract
    is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g →
      is-limit-sequence-ℝ
        ( sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
          ( [a,b])
          ( f)
          ( x)
          ( y))
        ( g x)
    is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
      H =
      let
        open
          do-syntax-trunc-Prop
            ( is-limit-prop-sequence-ℝ
              ( sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
                ( [a,b])
                ( f)
                ( x)
                ( y))
              ( g x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        seq-deriv =
          sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( x)
            ( y)
        nonzero-diff n =
          nonzero-diff-apart-ℝ
            ( real-sequence-accumulating-to-point-subset-ℝ
              ( subtype-proper-closed-interval-ℝ l1 [a,b])
              ( pr1 x)
              ( y)
              ( n))
            ( pr1 x)
            ( apart-sequence-accumulating-to-point-subset-ℝ
              ( subtype-proper-closed-interval-ℝ l1 [a,b])
              ( pr1 x)
              ( y)
              ( n))
        real-nonzero-diff n = real-nonzero-ℝ (nonzero-diff n)
      in do
        (μ , is-mod-μ) ←
          is-limit-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( pr1 x)
            ( y)
        (ν , is-mod-ν) ← H
        intro-exists
          ( μ ∘ ν)
          ( λ ε n N≤n →
            neighborhood-dist-ℝ
              ( ε)
              ( seq-deriv n)
              ( g x)
              ( chain-of-inequalities
                dist-ℝ (seq-deriv n) (g x)
                ≤ dist-ℝ (seq-deriv n) (g x *ℝ one-ℝ)
                  by
                    leq-eq-ℝ (ap-dist-ℝ refl (inv (right-unit-law-mul-ℝ (g x))))
                ≤ dist-ℝ
                    ( (f (pr1 y n) -ℝ f x) *ℝ
                      real-inv-nonzero-ℝ (nonzero-diff n))
                    ( g x *ℝ
                      ( real-nonzero-diff n *ℝ
                        real-inv-nonzero-ℝ (nonzero-diff n)))
                  by
                    leq-sim-ℝ
                      ( preserves-dist-right-sim-ℝ
                        ( preserves-sim-left-mul-ℝ _ _ _
                          ( symmetric-sim-ℝ
                            ( right-inverse-law-mul-nonzero-ℝ
                              ( nonzero-diff n)))))
                ≤ dist-ℝ
                    ( (f (pr1 y n) -ℝ f x) *ℝ
                      real-inv-nonzero-ℝ (nonzero-diff n))
                    ( (g x *ℝ real-nonzero-diff n) *ℝ
                      real-inv-nonzero-ℝ (nonzero-diff n))
                  by leq-eq-ℝ (ap-dist-ℝ refl (inv (associative-mul-ℝ _ _ _)))
                ≤ dist-ℝ
                    ( f (pr1 y n) -ℝ f x)
                    ( g x *ℝ (pr1 (pr1 y n) -ℝ pr1 x)) *ℝ
                  abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))
                  by leq-eq-ℝ (inv (right-distributive-abs-mul-dist-ℝ _ _ _))
                ≤ ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 (pr1 y n))) *ℝ
                  ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n)))
                  by
                    preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ _)
                      ( is-mod-ν
                        ( ε)
                        ( x)
                        ( pr1 y n)
                        ( is-symmetric-neighborhood-ℝ
                          ( ν ε)
                          ( pr1 (pr1 y n))
                          ( pr1 x)
                          ( is-mod-μ (ν ε) n N≤n)))
                ≤ ( real-ℚ⁺ ε) *ℝ
                  ( ( abs-ℝ (pr1 x -ℝ pr1 (pr1 y n))) *ℝ
                    ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))))
                  by leq-eq-ℝ (associative-mul-ℝ _ _ _)
                ≤ ( real-ℚ⁺ ε) *ℝ
                  ( ( abs-ℝ (pr1 (pr1 y n) -ℝ pr1 x)) *ℝ
                    ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ refl (ap-mul-ℝ (commutative-dist-ℝ _ _) refl))
                ≤ ( real-ℚ⁺ ε) *ℝ
                  ( abs-ℝ
                    ( ( pr1 (pr1 y n) -ℝ pr1 x) *ℝ
                      ( real-inv-nonzero-ℝ (nonzero-diff n))))
                  by leq-eq-ℝ (ap-mul-ℝ refl (inv (abs-mul-ℝ _ _)))
                ≤ real-ℚ⁺ ε *ℝ abs-ℝ one-ℝ
                  by
                    leq-sim-ℝ
                      ( preserves-sim-left-mul-ℝ _ _ _
                        ( preserves-sim-abs-ℝ
                          ( right-inverse-law-mul-nonzero-ℝ (nonzero-diff n))))
                ≤ real-ℚ⁺ ε *ℝ one-ℝ
                  by leq-eq-ℝ (ap-mul-ℝ refl (abs-real-ℝ⁰⁺ one-ℝ⁰⁺))
                ≤ real-ℚ⁺ ε
                  by leq-eq-ℝ (right-unit-law-mul-ℝ _)))
```

### Any two derivatives of a function are homotopic

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (h : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  where

  abstract
    htpy-is-derivative-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g →
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f h →
      g ~ h
    htpy-is-derivative-real-function-proper-closed-interval-ℝ
      G H x'@(x , x∈[a,b]) =
      let
        open do-syntax-trunc-Prop (Id-Prop (ℝ-Set (l1 ⊔ l2)) (g x') (h x'))
      in do
        y ←
          is-sequential-accumulation-point-is-accumulation-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( x)
            ( is-accumulation-point-is-in-proper-closed-interval-ℝ
              ( [a,b])
              ( x)
              ( x∈[a,b]))
        eq-is-limit-sequence-ℝ
          ( sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( x')
            ( y))
          ( g x')
          ( h x')
          ( is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( g)
            ( x')
            ( y)
            ( G))
          ( is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( h)
            ( x')
            ( y)
            ( H))
```

### Being differentiable is a proposition

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  where

  is-differentiable-real-function-proper-closed-interval-ℝ :
    UU (lsuc l1 ⊔ lsuc l2)
  is-differentiable-real-function-proper-closed-interval-ℝ =
    Σ ( type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
      ( is-derivative-real-function-proper-closed-interval-ℝ [a,b] f)

  abstract
    eq-is-derivative-real-function-proper-closed-interval-ℝ :
      (g h : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2)) →
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g →
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f h →
      g ＝ h
    eq-is-derivative-real-function-proper-closed-interval-ℝ g h G H =
      eq-htpy
        ( htpy-is-derivative-real-function-proper-closed-interval-ℝ
          ( [a,b])
          ( f)
          ( g)
          ( h)
          ( G)
          ( H))

    all-elements-equal-is-differentiable-real-function-proper-closed-interval-ℝ :
      all-elements-equal
        ( is-differentiable-real-function-proper-closed-interval-ℝ)
    all-elements-equal-is-differentiable-real-function-proper-closed-interval-ℝ
      (g , G) (h , H) =
      eq-type-subtype
        ( is-derivative-prop-real-function-proper-closed-interval-ℝ [a,b] f)
        ( eq-is-derivative-real-function-proper-closed-interval-ℝ g h G H)

    is-prop-is-differentiable-real-function-proper-closed-interval-ℝ :
      is-prop is-differentiable-real-function-proper-closed-interval-ℝ
    is-prop-is-differentiable-real-function-proper-closed-interval-ℝ =
      is-prop-all-elements-equal
        all-elements-equal-is-differentiable-real-function-proper-closed-interval-ℝ

  is-differentiable-prop-real-function-proper-closed-interval-ℝ :
    Prop (lsuc l1 ⊔ lsuc l2)
  is-differentiable-prop-real-function-proper-closed-interval-ℝ =
    ( is-differentiable-real-function-proper-closed-interval-ℝ ,
      is-prop-is-differentiable-real-function-proper-closed-interval-ℝ)
```

### A derivative of a real function on a proper closed interval is uniformly continuous

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f f')
  where

  abstract
    is-ucont-map-is-derivative-real-function-proper-closed-interval-ℝ :
      is-ucont-map-proper-closed-interval-ℝ [a,b] f'
    is-ucont-map-is-derivative-real-function-proper-closed-interval-ℝ =
      {!   !}
```
