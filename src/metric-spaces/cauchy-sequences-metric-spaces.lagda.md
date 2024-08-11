# Cauchy sequences in metric spaces

```agda
module metric-spaces.cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Cauchy sequences in metric spaces are sequences that satisfy the Cauchy
criterion. This follows Definition 11.2.9 of {{#cite UF13}}.

## Definitions

### Cauchy sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  where

  is-modulus-cauchy-prop-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → Prop l
  is-modulus-cauchy-prop-Sequence-Metric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        ( Π-Prop
          ( ℕ)
          ( λ (m : ℕ) →
            hom-Prop
              ( leq-ℕ-Prop N n)
              ( hom-Prop
                ( leq-ℕ-Prop N m)
                ( neighbourhood-Metric-Space M d (u n) (u m))))))

  is-modulus-cauchy-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → UU l
  is-modulus-cauchy-Sequence-Metric-Space d N =
    type-Prop (is-modulus-cauchy-prop-Sequence-Metric-Space d N)

  is-cauchy-Sequence-Metric-Space : UU l
  is-cauchy-Sequence-Metric-Space =
    (d : ℚ⁺) → Σ ℕ (is-modulus-cauchy-Sequence-Metric-Space d)
```

### Convergent sequences in metric spaces are Cauchy sequences

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  where

  is-cauchy-is-convergent-Sequence-Metric-Space :
    is-convergent-Sequence-Metric-Space M u →
    is-cauchy-Sequence-Metric-Space M u
  is-cauchy-is-convergent-Sequence-Metric-Space (x , H) d = (N , α)
    where
      d₂ : ℚ⁺
      d₂ = mediant-zero-ℚ⁺ d

      d₁ : ℚ⁺
      d₁ = le-diff-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d)

      Np : ℕ
      Np = modulus-limit-Sequence-Metric-Space M u x H d₁

      Nq : ℕ
      Nq = modulus-limit-Sequence-Metric-Space M u x H d₂

      N : ℕ
      N = max-ℕ Np Nq

      α : is-modulus-cauchy-Sequence-Metric-Space M u d N
      α p q I J =
        tr
          ( λ d' → is-in-neighbourhood-Metric-Space M d' (u p) (u q))
          ( left-diff-law-add-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d))
          ( is-triangular-neighbourhood-Metric-Space M
            ( u p)
            ( x)
            ( u q)
            ( d₁)
            ( d₂)
            ( γ)
            ( is-symmetric-neighbourhood-Metric-Space M d₁ x (u p) β))
        where
          β : is-in-neighbourhood-Metric-Space M d₁ x (u p)
          β =
            is-modulus-modulus-limit-Sequence-Metric-Space M u x H d₁ p
              ( transitive-leq-ℕ Np N p I
                ( leq-left-leq-max-ℕ N Np Nq (refl-leq-ℕ N)))

          γ : is-in-neighbourhood-Metric-Space M d₂ x (u q)
          γ =
            is-modulus-modulus-limit-Sequence-Metric-Space M u x H d₂ q
              ( transitive-leq-ℕ Nq N q J
                ( leq-right-leq-max-ℕ N Np Nq (refl-leq-ℕ N)))
```

## References

{{#bibliography}}
