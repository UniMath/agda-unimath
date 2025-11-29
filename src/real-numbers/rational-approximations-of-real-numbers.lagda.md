# Rational approximations of real numbers

```agda
module real-numbers.rational-approximations-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.metric-space-of-real-numbers
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.dependent-pair-types
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import foundation.existential-quantification
open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import foundation.universe-levels
```

</details>

## Idea

## Definition

```agda
rational-approximation-ℝ : {l : Level} → ℝ l → ℚ⁺ → UU l
rational-approximation-ℝ {l} x ε =
  Σ ℚ (λ q → neighborhood-ℝ l ε x (raise-real-ℚ l q))
```

## Properties

### Any real number can be approximated to any positive rational `ε`

```agda
abstract opaque
  unfolding neighborhood-ℝ

  exists-rational-approximation-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    exists ℚ (λ q → neighborhood-prop-ℝ l ε x (raise-real-ℚ l q))
  exists-rational-approximation-ℝ {l} x ε =
    let
      open
        do-syntax-trunc-Prop (∃ ℚ (λ q → neighborhood-prop-ℝ l ε x (raise-real-ℚ l q)))
    in do
      ((p , q) , q<p+ε , p<x , x<q) ← is-arithmetically-located-ℝ x ε
      intro-exists
        ( p)
        ( ( λ r r+ε<p → {!   !}) ,
          ( λ r r+ε<x → {!   !}))
```
