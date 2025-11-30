# Rational approximations of real numbers

```agda
module real-numbers.rational-approximations-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import metric-spaces.dense-subsets-metric-spaces

open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A
{{#concept "rational approximation" Disambiguation="of a real number" Agda=rational-approximation-ℝ}}
of a [real number](real-numbers.dedekind-real-numbers.md) `x` to some
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`
is a [rational number](elementary-number-theory.rational-numbers.md) whose
[canonical embedding](real-numbers.rational-real-numbers.md) in the real numbers
is within an `ε`-neighborhood of `x` in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

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
  unfolding neighborhood-ℝ real-ℚ

  exists-rational-approximation-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    exists ℚ (λ q → neighborhood-prop-ℝ l ε x (raise-real-ℚ l q))
  exists-rational-approximation-ℝ {l} x ε⁺@(ε , _) =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ℚ (λ q → neighborhood-prop-ℝ l ε⁺ x (raise-real-ℚ l q)))
    in do
      ((p , q) , q<p+ε , p<x , x<q) ← is-arithmetically-located-ℝ x ε⁺
      intro-exists
        ( p)
        ( ( λ r r+ε<p →
            le-lower-cut-ℝ
              ( x)
              ( transitive-le-ℚ
                ( r)
                ( r +ℚ ε)
                ( p)
                ( map-inv-raise r+ε<p)
                ( le-right-add-rational-ℚ⁺ r ε⁺))
              ( p<x)) ,
          ( λ r r+ε<x →
            map-raise
              ( reflects-le-left-add-ℚ
                ( ε)
                ( r)
                ( p)
                ( transitive-le-ℚ
                  ( r +ℚ ε)
                  ( q)
                  ( p +ℚ ε)
                  ( q<p+ε)
                  ( le-lower-upper-cut-ℝ x r+ε<x x<q)))))
```
