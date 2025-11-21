# Derivatives of real functions on proper closed intervals of ℝ

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.derivatives-of-real-functions-on-proper-closed-intervals where
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
numbers, `g` is a {{#concept "derivative" WD="derivative" WDID=Q29175}} of `f`
if there [exists](foundation.existential-quantification.md) a modulus function
`μ` such that for `ε : ℚ⁺` and any `x` and `y` in `[a, b]` within a
`μ ε`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, $$|f(y) - f(x) - g(x)(y - x)| \leq ε|y - x|$$.

## Definition

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  where

  is-modulus-derivative-prop-real-function-proper-closed-interval-ℝ :
    (ℚ⁺ → ℚ⁺) → Prop (lsuc l1 ⊔ l2)
  is-modulus-derivative-prop-real-function-proper-closed-interval-ℝ μ =
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

  is-modulus-derivative-real-function-proper-closed-interval-ℝ :
    (ℚ⁺ → ℚ⁺) → UU (lsuc l1 ⊔ l2)
  is-modulus-derivative-real-function-proper-closed-interval-ℝ =
    is-in-subtype
      ( is-modulus-derivative-prop-real-function-proper-closed-interval-ℝ)

  is-derivative-prop-real-function-proper-closed-interval-ℝ :
    Prop (lsuc l1 ⊔ l2)
  is-derivative-prop-real-function-proper-closed-interval-ℝ =
    is-inhabited-subtype-Prop
      ( is-modulus-derivative-prop-real-function-proper-closed-interval-ℝ)

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

  is-derivative-modulus-real-function-proper-closed-interval-ℝ :
    ( (ε : ℚ⁺) →
      Σ ( ℚ⁺)
        ( λ δ →
          (x y : type-proper-closed-interval-ℝ l1 [a,b]) →
          neighborhood-ℝ l1 δ (pr1 x) (pr1 y) →
          leq-ℝ
            ( dist-ℝ (f y -ℝ f x) (g x *ℝ (pr1 y -ℝ pr1 x)))
            ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)))) →
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g
  is-derivative-modulus-real-function-proper-closed-interval-ℝ μ =
    intro-exists (pr1 ∘ μ) (pr2 ∘ μ)
```

### If `g` is a derivative of `f`, and `aₙ` is a sequence apart from but approaching `x`, and the limit exists, `g x` is equal to the limit as `n → ∞` of `(f aₙ - f x)/(aₙ - x)`

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (x : type-proper-closed-interval-ℝ l1 [a,b])
  (y :
    sequence-approaching-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( pr1 x))
  where

  sequence-derivative-approaching-point-proper-closed-interval-ℝ :
    sequence (ℝ (l1 ⊔ l2))
  sequence-derivative-approaching-point-proper-closed-interval-ℝ n =
    (f (pr1 y n) -ℝ f x) *ℝ
    real-inv-nonzero-ℝ
      ( nonzero-diff-apart-ℝ
        ( real-sequence-approaching-point-subset-ℝ
          ( subtype-proper-closed-interval-ℝ l1 [a,b])
          ( pr1 x)
          ( y)
          ( n))
        ( pr1 x)
        ( apart-sequence-approaching-point-subset-ℝ
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
    sequence-approaching-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( pr1 x))
  where

  abstract
    is-limit-sequence-derivative-approaching-point-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ [a,b] f g →
      is-limit-sequence-ℝ
        ( sequence-derivative-approaching-point-proper-closed-interval-ℝ
          ( [a,b])
          ( f)
          ( x)
          ( y))
        ( g x)
    is-limit-sequence-derivative-approaching-point-proper-closed-interval-ℝ H =
      let
        open
          do-syntax-trunc-Prop
            ( is-limit-prop-sequence-ℝ
              ( sequence-derivative-approaching-point-proper-closed-interval-ℝ
                ( [a,b])
                ( f)
                ( x)
                ( y))
              ( g x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        seq-deriv =
          sequence-derivative-approaching-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( x)
            ( y)
        nonzero-diff n =
          nonzero-diff-apart-ℝ
            ( real-sequence-approaching-point-subset-ℝ
              ( subtype-proper-closed-interval-ℝ l1 [a,b])
              ( pr1 x)
              ( y)
              ( n))
            ( pr1 x)
            ( apart-sequence-approaching-point-subset-ℝ
              ( subtype-proper-closed-interval-ℝ l1 [a,b])
              ( pr1 x)
              ( y)
              ( n))
        real-nonzero-diff n = real-nonzero-ℝ (nonzero-diff n)
      in do
        (μ , is-mod-μ) ←
          is-limit-sequence-approaching-point-subset-ℝ
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
                      ( real-inv-nonzero-ℝ (nonzero-diff n)))
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
          ( sequence-derivative-approaching-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( x')
            ( y))
          ( g x')
          ( h x')
          ( is-limit-sequence-derivative-approaching-point-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( g)
            ( x')
            ( y)
            ( G))
          ( is-limit-sequence-derivative-approaching-point-proper-closed-interval-ℝ
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
    all-elements-equal-is-differentiable-real-function-proper-closed-interval-ℝ :
      all-elements-equal
        ( is-differentiable-real-function-proper-closed-interval-ℝ)
    all-elements-equal-is-differentiable-real-function-proper-closed-interval-ℝ
      (g , G) (h , H) =
      eq-type-subtype
        ( is-derivative-prop-real-function-proper-closed-interval-ℝ [a,b] f)
        ( eq-htpy
          ( htpy-is-derivative-real-function-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
            ( g)
            ( h)
            ( G)
            ( H)))

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

### The derivative of `f + g` is `f' + g'`

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l3)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (g' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l3))
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f f')
  (is-derivative-g-g' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] g g')
  where

  abstract
    is-derivative-add-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ x → f x +ℝ g x)
        ( λ x → f' x +ℝ g' x)
    is-derivative-add-real-function-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( λ x → f x +ℝ g x)
              ( λ x → f' x +ℝ g' x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (μ , is-mod-μ) ← is-derivative-f-f'
        (ν , is-mod-ν) ← is-derivative-g-g'
        is-derivative-modulus-real-function-proper-closed-interval-ℝ [a,b] _ _
          ( λ ε →
            let
              (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
            in
              ( min-ℚ⁺ (μ ε₁) (ν ε₂) ,
                λ x y Nxy →
                  chain-of-inequalities
                    dist-ℝ
                      ( (f y +ℝ g y) -ℝ (f x +ℝ g x))
                      ( (f' x +ℝ g' x) *ℝ (pr1 y -ℝ pr1 x))
                    ≤ dist-ℝ
                        ( (f y -ℝ f x) +ℝ (g y -ℝ g x))
                        ( f' x *ℝ (pr1 y -ℝ pr1 x) +ℝ g' x *ℝ (pr1 y -ℝ pr1 x))
                      by
                        leq-eq-ℝ
                          ( ap-dist-ℝ
                            ( interchange-law-diff-add-ℝ _ _ _ _)
                            ( right-distributive-mul-add-ℝ _ _ _))
                    ≤ abs-ℝ
                        ( ( (f y -ℝ f x) -ℝ f' x *ℝ (pr1 y -ℝ pr1 x)) +ℝ
                          ( (g y -ℝ g x) -ℝ g' x *ℝ (pr1 y -ℝ pr1 x)))
                      by
                        leq-eq-ℝ (ap abs-ℝ (interchange-law-diff-add-ℝ _ _ _ _))
                    ≤ ( dist-ℝ (f y -ℝ f x) (f' x *ℝ (pr1 y -ℝ pr1 x))) +ℝ
                      ( dist-ℝ (g y -ℝ g x) (g' x *ℝ (pr1 y -ℝ pr1 x)))
                      by triangle-inequality-abs-ℝ _ _
                    ≤ ( real-ℚ⁺ ε₁ *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( real-ℚ⁺ ε₂ *ℝ dist-ℝ (pr1 x) (pr1 y))
                      by
                        preserves-leq-add-ℝ
                          ( is-mod-μ
                            ( ε₁)
                            ( x)
                            ( y)
                            ( weakly-monotonic-neighborhood-Metric-Space
                              ( metric-space-ℝ l1)
                              ( pr1 x)
                              ( pr1 y)
                              ( min-ℚ⁺ (μ ε₁) (ν ε₂))
                              ( μ ε₁)
                              ( leq-left-min-ℚ⁺ _ _)
                              ( Nxy)))
                          ( is-mod-ν
                            ( ε₂)
                            ( x)
                            ( y)
                            ( weakly-monotonic-neighborhood-Metric-Space
                              ( metric-space-ℝ l1)
                              ( pr1 x)
                              ( pr1 y)
                              ( min-ℚ⁺ (μ ε₁) (ν ε₂))
                              ( ν ε₂)
                              ( leq-right-min-ℚ⁺ _ _)
                              ( Nxy)))
                    ≤ (real-ℚ⁺ ε₁ +ℝ real-ℚ⁺ ε₂) *ℝ dist-ℝ (pr1 x) (pr1 y)
                      by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
                    ≤ real-ℚ⁺ (ε₁ +ℚ⁺ ε₂) *ℝ dist-ℝ (pr1 x) (pr1 y)
                      by leq-eq-ℝ (ap-mul-ℝ (add-real-ℚ _ _) refl)
                    ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                      by leq-eq-ℝ (ap-mul-ℝ (ap real-ℚ⁺ ε₁+ε₂=ε) refl)))
```

### The derivative of `cf` is `cf'`

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f f')
  (c : ℝ l3)
  where

  abstract
    is-derivative-scalar-mul-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ x → c *ℝ f x)
        ( λ x → c *ℝ f' x)
    is-derivative-scalar-mul-real-function-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( λ x → c *ℝ f x)
              ( λ x → c *ℝ f' x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (μ , is-mod-μ) ← is-derivative-f-f'
        (q , |c|<q) ← exists-ℚ⁺-le-ℝ⁰⁺ (nonnegative-abs-ℝ c)
        is-derivative-modulus-real-function-proper-closed-interval-ℝ [a,b] _ _
          ( λ ε →
            ( μ (ε *ℚ⁺ inv-ℚ⁺ q) ,
              λ x y N⟨ε/q⟩xy →
                chain-of-inequalities
                  dist-ℝ (c *ℝ f y -ℝ c *ℝ f x) (c *ℝ f' x *ℝ (pr1 y -ℝ pr1 x))
                  ≤ dist-ℝ (c *ℝ (f y -ℝ f x)) (c *ℝ (f' x *ℝ (pr1 y -ℝ pr1 x)))
                    by
                      leq-eq-ℝ
                        ( ap-dist-ℝ
                          ( inv (left-distributive-mul-diff-ℝ _ _ _))
                          ( associative-mul-ℝ _ _ _))
                  ≤ abs-ℝ c *ℝ dist-ℝ (f y -ℝ f x) (f' x *ℝ (pr1 y -ℝ pr1 x))
                    by leq-eq-ℝ (inv (left-distributive-abs-mul-dist-ℝ _ _ _))
                  ≤ ( real-ℚ⁺ q) *ℝ
                    ( real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ dist-ℝ (pr1 x) (pr1 y))
                    by
                      preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ c)
                        ( nonnegative-real-ℚ⁺ q)
                        ( nonnegative-dist-ℝ _ _)
                        ( nonnegative-real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ⁰⁺
                          nonnegative-dist-ℝ _ _)
                        ( leq-le-ℝ |c|<q)
                        ( is-mod-μ
                          ( ε *ℚ⁺ inv-ℚ⁺ q)
                          ( x)
                          ( y)
                          ( N⟨ε/q⟩xy))
                  ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                    by
                      leq-eq-ℝ
                        ( ( inv (associative-mul-ℝ _ _ _)) ∙
                          ( ap-mul-ℝ
                            ( ( mul-real-ℚ _ _) ∙
                              ( ap
                                ( real-ℚ⁺)
                                ( is-identity-right-conjugation-Ab
                                  ( abelian-group-mul-ℚ⁺)
                                  ( q)
                                  ( ε))))
                            ( refl)))))
```

### The derivative of a constant function is 0

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (c : ℝ l2)
  where

  abstract
    derivative-constant-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ _ → c)
        ( λ _ → raise-ℝ (l1 ⊔ l2) zero-ℝ)
    derivative-constant-real-function-proper-closed-interval-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-derivative-modulus-real-function-proper-closed-interval-ℝ [a,b] _ _
          ( λ ε →
            ( one-ℚ⁺ ,
              λ x y _ →
              chain-of-inequalities
                dist-ℝ (c -ℝ c) (raise-ℝ (l1 ⊔ l2) zero-ℝ *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ zero-ℝ zero-ℝ
                  by
                    leq-sim-ℝ
                      ( preserves-dist-sim-ℝ
                        ( right-inverse-law-add-ℝ c)
                        ( similarity-reasoning-ℝ
                            raise-ℝ (l1 ⊔ l2) zero-ℝ *ℝ (pr1 y -ℝ pr1 x)
                            ~ℝ zero-ℝ *ℝ (pr1 y -ℝ pr1 x)
                              by
                                preserves-sim-right-mul-ℝ _ _ _
                                  ( symmetric-sim-ℝ (sim-raise-ℝ _ zero-ℝ))
                            ~ℝ zero-ℝ
                              by left-zero-law-mul-ℝ _))
                ≤ zero-ℝ
                  by leq-sim-ℝ (diagonal-dist-ℝ zero-ℝ)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    is-nonnegative-real-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))
```

### The derivative of the identity function is 1

```agda
module _
  {l : Level}
  ([a,b] : proper-closed-interval-ℝ l l)
  where

  abstract
    derivative-id-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( pr1)
        ( λ _ → raise-ℝ l one-ℝ)
    derivative-id-real-function-proper-closed-interval-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-derivative-modulus-real-function-proper-closed-interval-ℝ [a,b] _ _
          ( λ ε →
            ( one-ℚ⁺ ,
              λ x y _ →
                chain-of-inequalities
                  dist-ℝ (pr1 y -ℝ pr1 x) (raise-ℝ l one-ℝ *ℝ (pr1 y -ℝ pr1 x))
                  ≤ dist-ℝ (pr1 y -ℝ pr1 x) (pr1 y -ℝ pr1 x)
                    by
                      leq-eq-ℝ
                        ( ap-dist-ℝ
                          ( refl)
                          ( ( eq-sim-ℝ
                              ( preserves-sim-right-mul-ℝ _ _ _
                                ( symmetric-sim-ℝ (sim-raise-ℝ _ _)))) ∙
                            ( left-unit-law-mul-ℝ _)))
                  ≤ zero-ℝ
                    by leq-sim-ℝ (diagonal-dist-ℝ _)
                  ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                    by
                      is-nonnegative-real-ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))
```
