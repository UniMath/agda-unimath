# Cauchy sequences in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cauchy-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.decreasing-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.increasing-sequences-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in the Dedekind real numbers" Agda=cauchy-sequence-ℝ}}
is a [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) in the
[metric space](metric-spaces.metric-spaces.md) of
[real numbers](real-numbers.dedekind-real-numbers.md). Because the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
[is complete](real-numbers.cauchy-completeness-dedekind-real-numbers.md), a
[sequence](lists.sequences.md) of real numbers has a
[convergence modulus](metric-spaces.convergent-sequences-metric-spaces.md)
[if and only if](foundation.logical-equivalences.md) it is Cauchy.

## Definition

```agda
is-cauchy-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU l
is-cauchy-sequence-ℝ {l} = is-cauchy-sequence-Metric-Space (metric-space-ℝ l)

cauchy-sequence-ℝ : (l : Level) → UU (lsuc l)
cauchy-sequence-ℝ l = cauchy-sequence-Metric-Space (metric-space-ℝ l)

seq-cauchy-sequence-ℝ :
  {l : Level} → cauchy-sequence-ℝ l → sequence (ℝ l)
seq-cauchy-sequence-ℝ = pr1
```

## Properties

### All Cauchy sequences in ℝ have a limit

```agda
opaque
  has-limit-cauchy-sequence-ℝ :
    {l : Level} (u : cauchy-sequence-ℝ l) →
    has-limit-sequence-ℝ (seq-cauchy-sequence-ℝ u)
  has-limit-cauchy-sequence-ℝ {l} =
    has-limit-cauchy-sequence-Complete-Metric-Space (complete-metric-space-ℝ l)

  lim-cauchy-sequence-ℝ : {l : Level} → cauchy-sequence-ℝ l → ℝ l
  lim-cauchy-sequence-ℝ {l} =
    limit-cauchy-sequence-Complete-Metric-Space (complete-metric-space-ℝ l)

  abstract
    is-limit-lim-cauchy-sequence-ℝ :
      {l : Level} (s : cauchy-sequence-ℝ l) →
      is-limit-sequence-ℝ (seq-cauchy-sequence-ℝ s) (lim-cauchy-sequence-ℝ s)
    is-limit-lim-cauchy-sequence-ℝ {l} =
      is-limit-limit-cauchy-sequence-Complete-Metric-Space
        ( complete-metric-space-ℝ l)
```

### The sum of Cauchy sequences is a Cauchy sequence

```agda
add-cauchy-sequence-ℝ :
  {l1 l2 : Level} → cauchy-sequence-ℝ l1 → cauchy-sequence-ℝ l2 →
  cauchy-sequence-ℝ (l1 ⊔ l2)
add-cauchy-sequence-ℝ {l1} {l2} u v =
  map-modulated-ucont-map-cauchy-sequence-Metric-Space
    ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
    ( metric-space-ℝ (l1 ⊔ l2))
    ( modulated-ucont-map-product-add-pair-ℝ l1 l2)
    ( pair-cauchy-sequence-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-ℝ l2)
      ( u)
      ( v))
```

### Squeeze theorem

If `aₙ ≤ bₙ ≤ cₙ`, where `aₙ` is increasing, `cₙ` is decreasing, and `cₙ - aₙ`
[approaches 0](real-numbers.real-sequences-approximating-zero.md), then there
exists a Cauchy modulus for `bₙ`.

```agda
module _
  {l1 l2 l3 : Level}
  (a : sequence (ℝ l1))
  (b : sequence (ℝ l2))
  (c : sequence (ℝ l3))
  (a≤b : (n : ℕ) → leq-ℝ (a n) (b n))
  (b≤c : (n : ℕ) → leq-ℝ (b n) (c n))
  (is-increasing-a : is-increasing-sequence-ℝ a)
  (is-decreasing-c : is-decreasing-sequence-ℝ c)
  (c-a→0 : is-zero-limit-sequence-ℝ (λ n → c n -ℝ a n))
  where

  abstract
    is-cauchy-squeeze-theorem-sequence-ℝ :
      is-inhabited (is-cauchy-sequence-ℝ b)
    is-cauchy-squeeze-theorem-sequence-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open do-syntax-trunc-Prop (is-inhabited-Prop (is-cauchy-sequence-ℝ b))
      in do
        (μ , is-mod-μ) ← c-a→0
        let
          bound :
            (ε : ℚ⁺) (m k : ℕ) → leq-ℕ (μ ε) m → leq-ℕ (μ ε) k →
            leq-ℝ (b m) (b k +ℝ real-ℚ⁺ ε)
          bound ε m k με≤m με≤k =
            chain-of-inequalities
              b m
              ≤ c m
                by b≤c m
              ≤ c (μ ε)
                by is-decreasing-c (μ ε) m με≤m
              ≤ a k +ℝ (c (μ ε) -ℝ a k)
                by leq-sim-ℝ' (add-right-diff-ℝ (a k) (c (μ ε)))
              ≤ a k +ℝ (c (μ ε) -ℝ a (μ ε))
                by
                  preserves-leq-left-add-ℝ _ _ _
                    ( preserves-leq-left-add-ℝ _ _ _
                      ( neg-leq-ℝ
                        ( is-increasing-a (μ ε) k με≤k)))
              ≤ b k +ℝ (raise-zero-ℝ (l1 ⊔ l3) +ℝ real-ℚ⁺ ε)
                by
                  preserves-leq-add-ℝ
                    ( a≤b k)
                    ( left-leq-real-bound-neighborhood-ℝ
                      ( ε)
                      ( c (μ ε) -ℝ a (μ ε))
                      ( raise-zero-ℝ (l1 ⊔ l3))
                      ( is-mod-μ ε (μ ε) (refl-leq-ℕ (μ ε))))
              ≤ b k +ℝ (zero-ℝ +ℝ real-ℚ⁺ ε)
                by
                  leq-sim-ℝ
                    ( preserves-sim-left-add-ℝ _ _ _
                      ( preserves-sim-right-add-ℝ _ _ _
                        ( sim-raise-ℝ' _ zero-ℝ)))
              ≤ b k +ℝ real-ℚ⁺ ε
                by leq-eq-ℝ (ap-add-ℝ refl (left-unit-law-add-ℝ _))
        unit-trunc-Prop
          ( λ ε →
            ( μ ε ,
              λ m k με≤m με≤k →
              neighborhood-real-bound-each-leq-ℝ
                ( ε)
                ( b m)
                ( b k)
                ( bound ε m k με≤m με≤k)
                ( bound ε k m με≤k με≤m)))
```

### If a sequence has a limit, there exists a modulus making it a Cauchy sequence

```agda
abstract
  exists-cauchy-modulus-has-limit-sequence-ℝ :
    {l : Level} (σ : sequence (ℝ l)) →
    has-limit-sequence-ℝ σ →
    is-inhabited (is-cauchy-sequence-ℝ σ)
  exists-cauchy-modulus-has-limit-sequence-ℝ {l} σ (lim , is-lim) =
    map-is-inhabited
      ( is-cauchy-has-limit-modulus-sequence-Metric-Space
        ( metric-space-ℝ l)
        ( σ)
        ( lim))
      ( is-lim)
```
