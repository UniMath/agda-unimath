# Metrics of metric spaces are uniformly continuous

```agda
module metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.metrics-of-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

If `ρ` [is a metric](metric-spaces.metrics-of-metric-spaces.md) of the
[metric space](metric-spaces.metric-spaces.md) `M`, then it is a
[uniformly continuous map](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
from the
[product metric space](metric-spaces.cartesian-products-metric-spaces.md)
`M × M` to the metric space of
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md).

## Proof

```agda
module inequality-reasoning-Large-Poset
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  infixl 1 chain-of-inequalities_
  infixl 0 step-calculate-in-Large-Poset

  chain-of-inequalities_ :
    {l : Level} (x : type-Large-Poset P l) → leq-Large-Poset P x x
  chain-of-inequalities_ = refl-leq-Large-Poset P

  step-calculate-in-Large-Poset :
    {l1 l2 : Level} {x : type-Large-Poset P l1} {y : type-Large-Poset P l2} →
    leq-Large-Poset P x y →
    {l3 : Level} (z : type-Large-Poset P l3) →
    leq-Large-Poset P y z → leq-Large-Poset P x z
  step-calculate-in-Large-Poset {x = x} {y = y} u z v =
    transitive-leq-Large-Poset P x y z v u

  syntax step-calculate-in-Large-Poset u z v = u ≤ z by v
```

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  (H : is-metric-of-Metric-Space M ρ)
  where

  private
    open inequality-reasoning-Large-Poset ℝ-Large-Poset

    ρ' : type-Metric-Space M → type-Metric-Space M → ℝ l3
    ρ' x y = real-ℝ⁰⁺ (ρ x y)

    commutative-ρ' : (x y : type-Metric-Space M) → ρ' x y ＝ ρ' y x
    commutative-ρ' x y =
      ap real-ℝ⁰⁺ (is-symmetric-is-metric-of-Metric-Space M ρ H x y)

  abstract
    dist-metric-leq-metric-of-Metric-Space :
      (x y y' : type-Metric-Space M) →
      dist-ℝ (real-ℝ⁰⁺ (ρ x y)) (real-ℝ⁰⁺ (ρ x y')) ≤-ℝ real-ℝ⁰⁺ (ρ y y')
    dist-metric-leq-metric-of-Metric-Space x y y' =
      leq-dist-leq-add-ℝ _ _ _
        ( chain-of-inequalities
          ρ' x y
          ≤ ρ' x y' +ℝ ρ' y' y
            by is-triangular-is-metric-of-Metric-Space M ρ H x y' y
          ≤ ρ' y' y +ℝ ρ' x y' by leq-eq-ℝ _ _ (commutative-add-ℝ _ _)
          ≤ ρ' y y' +ℝ ρ' x y'
            by leq-eq-ℝ _ _ (ap-add-ℝ (commutative-ρ' y' y) refl))
        ( chain-of-inequalities
          ρ' x y'
          ≤ ρ' x y +ℝ ρ' y y'
            by is-triangular-is-metric-of-Metric-Space M ρ H x y y'
          ≤ ρ' y y' +ℝ ρ' x y by leq-eq-ℝ _ _ (commutative-add-ℝ _ _))

    is-uniformly-continuous-metric-of-Metric-Space :
      is-uniformly-continuous-function-Metric-Space
        ( product-Metric-Space M M)
        ( metric-space-ℝ⁰⁺ l3)
        ( ind-Σ ρ)
    is-uniformly-continuous-metric-of-Metric-Space =
      intro-exists
        ( modulus-le-double-le-ℚ⁺)
        ( λ (x , y) ε (x' , y') (Nε'xx' , Nε'yy') →
          let
            ε' = modulus-le-double-le-ℚ⁺ ε
            2ε'<ε = le-double-le-modulus-le-double-le-ℚ⁺ ε
          in
            neighborhood-dist-ℝ ε (ρ' x y) (ρ' x' y')
              ( chain-of-inequalities
                dist-ℝ (ρ' x y) (ρ' x' y')
                ≤ dist-ℝ (ρ' x y) (ρ' x y') +ℝ dist-ℝ (ρ' x y') (ρ' x' y')
                  by triangle-inequality-dist-ℝ _ _ _
                ≤ dist-ℝ (ρ' x y) (ρ' x y') +ℝ dist-ℝ (ρ' y' x) (ρ' y' x')
                  by
                    leq-eq-ℝ _ _
                      ( ap-add-ℝ
                        ( refl)
                        ( ap-binary
                          ( dist-ℝ)
                          ( commutative-ρ' x y')
                          ( commutative-ρ' x' y')))
                ≤ ρ' y y' +ℝ ρ' x x'
                  by
                    preserves-leq-add-ℝ _ _ _ _
                      ( dist-metric-leq-metric-of-Metric-Space x y y')
                      ( dist-metric-leq-metric-of-Metric-Space y' x x')
                ≤ real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε'
                  by
                    preserves-leq-add-ℝ _ _ _ _
                      ( forward-implication (H ε' y y') Nε'yy')
                      ( forward-implication (H ε' x x') Nε'xx')
                ≤ real-ℚ⁺ (ε' +ℚ⁺ ε') by leq-eq-ℝ _ _ (add-real-ℚ _ _)
                ≤ real-ℚ⁺ ε by preserves-leq-real-ℚ _ _ (leq-le-ℚ 2ε'<ε)))

  uniformly-continuous-metric-of-Metric-Space :
    uniformly-continuous-function-Metric-Space
      ( product-Metric-Space M M)
      ( metric-space-ℝ⁰⁺ l3)
  uniformly-continuous-metric-of-Metric-Space =
    ( ind-Σ ρ ,
      is-uniformly-continuous-metric-of-Metric-Space)
```
