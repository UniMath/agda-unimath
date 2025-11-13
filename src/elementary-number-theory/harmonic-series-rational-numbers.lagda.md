# The harmonic series of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.harmonic-series-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-nonnegative-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.series-rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications

open import group-theory.abelian-groups

open import order-theory.posets

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "harmonic series" WDID=Q464100 WD="harmonic series" Agda=harmonic-series-ℚ}}
is the sum $$Σ_{n=0}^{∞} \frac{1}{n}$$.

## Definition

```agda
harmonic-series-ℚ : series-ℚ
harmonic-series-ℚ = series-terms-ℚ reciprocal-rational-succ-ℕ
```

## Properties

### For any `k`, the `2ᵏ`th partial sum of the harmonic series is at least `1 + k/2`

```agda
abstract
  lower-bound-sum-harmonic-series-power-of-two-ℚ :
    (k : ℕ) →
    leq-ℚ
      ( one-ℚ +ℚ reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ k)
      ( partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 k))
  lower-bound-sum-harmonic-series-power-of-two-ℚ 0 =
    leq-eq-ℚ
      ( inv
        ( equational-reasoning
            partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 zero-ℕ)
            ＝ reciprocal-rational-succ-ℕ 0
              by compute-sum-one-element-ℚ _
            ＝ one-ℚ
              by ap rational-ℚ⁺ inv-one-ℚ⁺
            ＝ one-ℚ +ℚ zero-ℚ
              by inv (right-unit-law-add-ℚ one-ℚ)
            ＝ one-ℚ +ℚ reciprocal-rational-succ-ℕ 1 *ℚ zero-ℚ
              by ap-add-ℚ refl (inv (right-zero-law-mul-ℚ _))))
  lower-bound-sum-harmonic-series-power-of-two-ℚ (succ-ℕ n) =
    let
      open inequality-reasoning-Poset ℚ-Poset
    in
      chain-of-inequalities
        one-ℚ +ℚ reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ (succ-ℕ n)
        ≤ one-ℚ +ℚ
          (reciprocal-rational-succ-ℕ 1 *ℚ succ-ℚ (rational-ℕ n))
          by leq-eq-ℚ (ap-add-ℚ refl (ap-mul-ℚ refl (inv (succ-rational-ℕ n))))
        ≤ one-ℚ +ℚ
          ( reciprocal-rational-succ-ℕ 1 +ℚ
            reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ n)
          by leq-eq-ℚ (ap-add-ℚ refl (mul-right-succ-ℚ _ _))
        ≤ reciprocal-rational-succ-ℕ 1 +ℚ
          ( one-ℚ +ℚ
            reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ n)
          by leq-eq-ℚ (left-swap-add-ℚ _ _ _)
        ≤ reciprocal-rational-succ-ℕ 1 +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by
            preserves-leq-right-add-ℚ _ _ _
              ( lower-bound-sum-harmonic-series-power-of-two-ℚ n)
        ≤ ( rational-ℕ (exp-ℕ 2 n) *ℚ
            reciprocal-rational-succ-ℕ 1 *ℚ
            reciprocal-rational-ℕ⁺ (exp-ℕ⁺ (2 , (λ ())) n)) +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by
            leq-eq-ℚ
              ( ap-add-ℚ
                ( inv
                  ( ap
                    ( rational-ℚ⁺)
                    ( is-identity-left-conjugation-Ab
                      ( abelian-group-mul-ℚ⁺)
                      ( positive-rational-ℕ⁺ (exp-ℕ⁺ (2 , λ ()) n))
                      ( positive-reciprocal-rational-succ-ℕ 1))))
                ( refl))
        ≤ ( rational-ℕ (exp-ℕ 2 n) *ℚ
            ( reciprocal-rational-succ-ℕ 1 *ℚ
              reciprocal-rational-ℕ⁺ (exp-ℕ⁺ (2 , (λ ())) n))) +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by leq-eq-ℚ (ap-add-ℚ (associative-mul-ℚ _ _ _) refl)
        ≤ ( rational-ℕ (exp-ℕ 2 n) *ℚ
            ( reciprocal-rational-ℕ⁺ (exp-ℕ⁺ (2 , (λ ())) n) *ℚ
              reciprocal-rational-succ-ℕ 1)) +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by leq-eq-ℚ (ap-add-ℚ (ap-mul-ℚ refl (commutative-mul-ℚ _ _)) refl)
        ≤ ( rational-ℕ (exp-ℕ 2 n) *ℚ
            reciprocal-rational-ℕ⁺ (exp-ℕ⁺ (2 , λ ()) (succ-ℕ n))) +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by
            leq-eq-ℚ
              ( ap-add-ℚ
                ( ap-mul-ℚ
                  ( refl)
                  ( ( inv
                      ( distributive-reciprocal-mul-ℕ⁺
                        ( exp-ℕ⁺ (2 , λ ()) n)
                        ( 2 , λ ()))) ∙
                    ( ap
                      ( reciprocal-rational-ℕ⁺)
                      ( eq-nonzero-ℕ
                        { exp-ℕ⁺ (2 , λ ()) n *ℕ⁺ (2 , λ ())}
                        { exp-ℕ⁺ (2 , (λ ())) (succ-ℕ n)}
                        ( refl)))))
                ( refl))
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ _ → reciprocal-rational-ℕ⁺ (exp-ℕ⁺ (2 , (λ ())) (succ-ℕ n))) +ℚ
          partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
          by leq-eq-ℚ (ap-add-ℚ (inv (sum-constant-fin-sequence-ℚ _ _)) refl)
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ
                ( nat-Fin
                  ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
                  ( inr-coproduct-Fin (exp-ℕ 2 n) (exp-ℕ 2 n) k))) +ℚ
          sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k → reciprocal-rational-succ-ℕ (nat-Fin (exp-ℕ 2 n) k))
          by
            preserves-leq-left-add-ℚ _ _ _
              ( preserves-leq-sum-fin-sequence-ℚ
                ( exp-ℕ 2 n)
                ( _)
                ( _)
                ( λ k →
                  inv-leq-ℚ⁺ _ _
                    ( preserves-leq-rational-ℕ
                      ( leq-succ-le-ℕ
                        ( nat-Fin (exp-ℕ 2 n +ℕ exp-ℕ 2 n) _)
                        ( exp-ℕ 2 (succ-ℕ n))
                        ( inv-tr
                          ( le-ℕ _)
                          ( right-two-law-mul-ℕ _)
                          ( strict-upper-bound-nat-Fin _ _))))))
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ
                ( nat-Fin
                  ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
                  ( inr-coproduct-Fin (exp-ℕ 2 n) (exp-ℕ 2 n) k))) +ℚ
          sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ
                ( nat-Fin
                  ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
                  ( inl-coproduct-Fin (exp-ℕ 2 n) (exp-ℕ 2 n) k)))
          by
            leq-eq-ℚ
              ( ap-add-ℚ
                ( refl)
                ( ap
                  ( sum-fin-sequence-ℚ (exp-ℕ 2 n))
                  ( eq-htpy
                    ( λ k →
                      ap
                        ( reciprocal-rational-succ-ℕ)
                        ( inv (nat-inl-coproduct-Fin _ _ k))))))
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ
                ( nat-Fin
                  ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
                  ( inl-coproduct-Fin (exp-ℕ 2 n) (exp-ℕ 2 n) k))) +ℚ
          sum-fin-sequence-ℚ
            ( exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ
                ( nat-Fin
                  ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
                  ( inr-coproduct-Fin (exp-ℕ 2 n) (exp-ℕ 2 n) k)))
          by leq-eq-ℚ (commutative-add-ℚ _ _)
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 n +ℕ exp-ℕ 2 n)
            ( λ k →
              reciprocal-rational-succ-ℕ (nat-Fin (exp-ℕ 2 n +ℕ exp-ℕ 2 n) k))
          by leq-eq-ℚ (inv (split-sum-fin-sequence-ℚ _ _ _))
        ≤ sum-fin-sequence-ℚ
            ( exp-ℕ 2 (succ-ℕ n))
            ( reciprocal-rational-succ-ℕ ∘ nat-Fin (exp-ℕ 2 (succ-ℕ n)))
          by
            leq-eq-ℚ
              ( ap
                ( λ k →
                  sum-fin-sequence-ℚ k (reciprocal-rational-succ-ℕ ∘ nat-Fin k))
                ( inv (right-two-law-mul-ℕ _)))
```

### The harmonic series diverges

The divergence of the harmonic series is the
[34th](literature.100-theorems.md#34) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
abstract
  grows-without-bound-harmonic-series-ℚ :
    grows-without-bound-series-ℚ harmonic-series-ℚ
  grows-without-bound-harmonic-series-ℚ q =
    let
      open
        do-syntax-trunc-Prop
          ( ∃
            ( ℕ)
            ( λ N →
              Π-Prop
                ( ℕ)
                ( λ n →
                  hom-Prop
                    ( leq-ℕ-Prop N n)
                    ( leq-ℚ-Prop q (partial-sum-series-ℚ harmonic-series-ℚ n)))))
      open inequality-reasoning-Poset ℚ-Poset
    in do
      (n , 2q<n) ← exists-greater-natural-ℚ (rational-ℕ 2 *ℚ q)
      intro-exists
        ( exp-ℕ 2 n)
        ( λ k 2ⁿ≤k →
          chain-of-inequalities
            q
            ≤ reciprocal-rational-succ-ℕ 1 *ℚ (rational-ℕ 2 *ℚ q)
              by
                leq-eq-ℚ
                  ( inv
                    ( is-retraction-left-div-ℚ⁺
                      ( positive-rational-ℕ⁺ (2 , λ ()))
                      ( q)))
            ≤ reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ n
              by
                preserves-leq-left-mul-ℚ⁺
                  ( positive-reciprocal-rational-succ-ℕ 1)
                  ( _)
                  ( _)
                  ( leq-le-ℚ 2q<n)
            ≤ one-ℚ +ℚ reciprocal-rational-succ-ℕ 1 *ℚ rational-ℕ n
              by is-inflationary-map-left-add-rational-ℚ⁰⁺ one-ℚ⁰⁺ _
            ≤ partial-sum-series-ℚ harmonic-series-ℚ (exp-ℕ 2 n)
              by lower-bound-sum-harmonic-series-power-of-two-ℚ n
            ≤ partial-sum-series-ℚ harmonic-series-ℚ k
              by
                is-monotonic-partial-sum-is-nonnegative-term-series-ℚ
                  ( harmonic-series-ℚ)
                  ( λ m →
                    is-nonnegative-is-positive-ℚ
                      ( is-positive-rational-ℚ⁺
                        ( positive-reciprocal-rational-succ-ℕ m)))
                  ( exp-ℕ 2 n)
                  ( k)
                  ( 2ⁿ≤k))
```
