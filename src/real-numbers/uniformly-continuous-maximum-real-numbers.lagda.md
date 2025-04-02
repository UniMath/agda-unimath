# The maximum function on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.products-metric-spaces
open import metric-spaces.uniformly-continuous-binary-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maxima-minima-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.minimum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[The maximum function on the real numbers](real-numbers.maximum-real-numbers.md)
is a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
abstract
  modulus-of-continuity-max-ℝ : ℚ⁺ → ℚ⁺
  modulus-of-continuity-max-ℝ = id

  is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ :
    {l1 l2 : Level} →
    is-modulus-of-uniform-continuity-Metric-Space
      ( product-Metric-Space (metric-space-leq-ℝ l1) (metric-space-leq-ℝ l2))
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( ind-product max-ℝ)
      ( modulus-of-continuity-max-ℝ)
  is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ
    (a , b) ε⁺@(ε , _) (a' , b') (a~a' , b~b') =
      let
        εℝ : ℝ lzero
        εℝ = real-ℚ ε
        maxab-maxa'b'=max-min-a-a'-a-b'-min-b-a'-b-b' :
          max-ℝ a b -ℝ max-ℝ a' b' ＝
          max-ℝ (min-ℝ (a -ℝ a') (a -ℝ b')) (min-ℝ (b -ℝ a') (b -ℝ b'))
        maxab-maxa'b'=max-min-a-a'-a-b'-min-b-a'-b-b' =
          equational-reasoning
            max-ℝ a b -ℝ max-ℝ a' b'
            ＝ max-ℝ a b +ℝ min-ℝ (neg-ℝ a') (neg-ℝ b')
              by ap (max-ℝ a b +ℝ_) (neg-max-ℝ _ _)
            ＝
              max-ℝ
                ( a +ℝ min-ℝ (neg-ℝ a') (neg-ℝ b'))
                ( b +ℝ min-ℝ (neg-ℝ a') (neg-ℝ b'))
              by right-distributive-add-max-ℝ a b _
            ＝
              max-ℝ
                ( min-ℝ (a -ℝ a') (a -ℝ b'))
                ( min-ℝ (b -ℝ a') (b -ℝ b'))
              by
                ap-binary
                  ( max-ℝ)
                  ( left-distributive-add-min-ℝ _ _ _)
                  ( left-distributive-add-min-ℝ _ _ _)
        a-a'≤ε : leq-ℝ (a -ℝ a') εℝ
        a-a'≤ε = diff-bound-neighborhood-leq-ℝ ε⁺ a a' a~a'
        min-a-a'-a-b'≤ε : leq-ℝ (min-ℝ (a -ℝ a') (a -ℝ b')) εℝ
        min-a-a'-a-b'≤ε =
          transitive-leq-ℝ
            ( min-ℝ (a -ℝ a') (a -ℝ b'))
            ( a -ℝ a')
            ( εℝ)
            ( a-a'≤ε)
            ( leq-left-min-ℝ _ _)
        b-b'≤ε : leq-ℝ (b -ℝ b') εℝ
        b-b'≤ε = diff-bound-neighborhood-leq-ℝ ε⁺ b b' b~b'
        min-b-a'-b-b'≤ε : leq-ℝ (min-ℝ (b -ℝ a') (b -ℝ b')) εℝ
        min-b-a'-b-b'≤ε =
          transitive-leq-ℝ
            ( min-ℝ (b -ℝ a') (b -ℝ b'))
            ( b -ℝ b')
            ( εℝ)
            ( b-b'≤ε)
            ( leq-right-min-ℝ _ _)
        max-min-a-a'-a-b'-min-b-a'-b-b'≤ε :
          leq-ℝ
            ( max-ℝ (min-ℝ (a -ℝ a') (a -ℝ b')) (min-ℝ (b -ℝ a') (b -ℝ b')))
            ( εℝ)
        max-min-a-a'-a-b'-min-b-a'-b-b'≤ε =
          leq-max-leq-ℝ _ _ εℝ min-a-a'-a-b'≤ε min-b-a'-b-b'≤ε
        -⟨maxab-maxa'b'⟩=max-min-a'-a-a'-b-min-b'-a-b'-b :
          neg-ℝ (max-ℝ a b -ℝ max-ℝ a' b') ＝
          max-ℝ (min-ℝ (a' -ℝ a) (a' -ℝ b)) (min-ℝ (b' -ℝ a) (b' -ℝ b))
        -⟨maxab-maxa'b'⟩=max-min-a'-a-a'-b-min-b'-a-b'-b =
          equational-reasoning
            neg-ℝ (max-ℝ a b -ℝ max-ℝ a' b')
            ＝ max-ℝ a' b' -ℝ max-ℝ a b by distributive-neg-diff-ℝ _ _
            ＝ max-ℝ a' b' +ℝ min-ℝ (neg-ℝ a) (neg-ℝ b)
              by ap (max-ℝ a' b' +ℝ_) (neg-max-ℝ _ _)
            ＝
              max-ℝ
                ( a' +ℝ min-ℝ (neg-ℝ a) (neg-ℝ b))
                ( b' +ℝ min-ℝ (neg-ℝ a) (neg-ℝ b))
              by right-distributive-add-max-ℝ _ _ _
            ＝
              max-ℝ
                ( min-ℝ (a' -ℝ a) (a' -ℝ b))
                ( min-ℝ (b' -ℝ a) (b' -ℝ b))
              by
                ap-binary
                  ( max-ℝ)
                  ( left-distributive-add-min-ℝ _ _ _)
                  ( left-distributive-add-min-ℝ _ _ _)
        a'-a≤ε = reversed-diff-bound-neighborhood-leq-ℝ ε⁺ a a' a~a'
        b'-b≤ε = reversed-diff-bound-neighborhood-leq-ℝ ε⁺ b b' b~b'
        min-a'-a-a'-b≤ε =
          transitive-leq-ℝ
            ( min-ℝ (a' -ℝ a) (a' -ℝ b))
            ( a' -ℝ a)
            ( εℝ)
            ( a'-a≤ε)
            ( leq-left-min-ℝ _ _)
        min-b'-a-b'-b≤ε =
          transitive-leq-ℝ
            ( min-ℝ (b' -ℝ a) (b' -ℝ b))
            ( b' -ℝ b)
            ( εℝ)
            ( b'-b≤ε)
            ( leq-right-min-ℝ _ _)
        max-min-a'-a-a'-b-min-b'-a-b'-b≤ε =
          leq-max-leq-ℝ
            ( min-ℝ (a' -ℝ a) (a' -ℝ b))
            ( min-ℝ (b' -ℝ a) (b' -ℝ b))
            ( εℝ)
            ( min-a'-a-a'-b≤ε)
            ( min-b'-a-b'-b≤ε)
      in
        neighborhood-abs-diff-bound-leq-ℝ
          ( ε⁺)
          ( max-ℝ a b)
          ( max-ℝ a' b')
          ( leq-abs-leq-leq-neg-ℝ
            ( _)
            ( εℝ)
            ( inv-tr
              ( λ x → leq-ℝ x εℝ)
              ( maxab-maxa'b'=max-min-a-a'-a-b'-min-b-a'-b-b')
              ( max-min-a-a'-a-b'-min-b-a'-b-b'≤ε))
            ( inv-tr
              ( λ x → leq-ℝ x εℝ)
              ( -⟨maxab-maxa'b'⟩=max-min-a'-a-a'-b-min-b'-a-b'-b)
              ( max-min-a'-a-a'-b-min-b'-a-b'-b≤ε)))

  is-uniformly-continuous-max-ℝ :
    {l1 l2 : Level} →
    is-uniformly-continuous-binary-map-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( max-ℝ)
  is-uniformly-continuous-max-ℝ =
    intro-exists
      ( modulus-of-continuity-max-ℝ)
      ( is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ)
```
