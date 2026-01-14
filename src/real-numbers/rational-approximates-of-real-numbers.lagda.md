# Rational approximates of real numbers

```agda
module real-numbers.rational-approximates-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.dense-subsets-metric-spaces

open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A
{{#concept "rational approximate" Disambiguation="of a real number" Agda=rational-approximate-ℝ}}
of a [real number](real-numbers.dedekind-real-numbers.md) `x` to some
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`
is a [rational number](elementary-number-theory.rational-numbers.md) whose
[canonical embedding](real-numbers.rational-real-numbers.md) in the real numbers
is within an `ε`-neighborhood of `x` in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
rational-approximate-ℝ : {l : Level} → ℝ l → ℚ⁺ → UU l
rational-approximate-ℝ {l} x ε =
  Σ ℚ (λ q → neighborhood-ℝ l ε x (raise-real-ℚ l q))

rational-approximate-above-ℝ : {l : Level} → ℝ l → ℚ⁺ → UU l
rational-approximate-above-ℝ {l} x ε =
  Σ ℚ (λ q → is-in-upper-cut-ℝ x q × neighborhood-ℝ l ε x (raise-real-ℚ l q))

rational-approximate-below-ℝ : {l : Level} → ℝ l → ℚ⁺ → UU l
rational-approximate-below-ℝ {l} x ε =
  Σ ℚ (λ q → is-in-lower-cut-ℝ x q × neighborhood-ℝ l ε x (raise-real-ℚ l q))
```

## Properties

### Any real number can be approximated below to any positive rational precision `ε`

```agda
abstract opaque
  unfolding neighborhood-ℝ real-ℚ

  exists-rational-approximate-below-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    is-inhabited (rational-approximate-below-ℝ x ε)
  exists-rational-approximate-below-ℝ {l} x ε⁺@(ε , _) =
    map-trunc-Prop
      ( λ ((p , q) , q<p+ε , p<x , x<q) →
        ( p ,
          p<x ,
          ( λ r r+ε<p →
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
                  ( le-lower-upper-cut-ℝ x r+ε<x x<q))))))
      ( is-arithmetically-located-ℝ x ε⁺)
```

### Any real number can be approximated above to any positive rational precision `ε`

```agda
abstract opaque
  unfolding neighborhood-ℝ real-ℚ

  exists-rational-approximate-above-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    is-inhabited (rational-approximate-above-ℝ x ε)
  exists-rational-approximate-above-ℝ {l} x ε⁺@(ε , _) =
    map-trunc-Prop
      ( λ ((p , q) , q<p+ε , p<x , x<q) →
        ( q ,
          x<q ,
          ( λ r r+ε<q →
            le-lower-cut-ℝ
              ( x)
              ( reflects-le-left-add-ℚ ε r p
                ( transitive-le-ℚ
                  ( r +ℚ ε)
                  ( q)
                  ( p +ℚ ε)
                  ( q<p+ε)
                  ( map-inv-raise r+ε<q)))
              ( p<x)) ,
          ( λ r r+ε<x →
            map-raise
              ( le-lower-upper-cut-ℝ
                ( x)
                ( le-lower-cut-ℝ x (le-right-add-rational-ℚ⁺ r ε⁺) r+ε<x)
                ( x<q)))))
      ( is-arithmetically-located-ℝ x ε⁺)
```

### Any real number can be approximated to any rational precision `ε`

```agda
abstract
  exists-rational-approximate-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    type-trunc-Prop (rational-approximate-ℝ x ε)
  exists-rational-approximate-ℝ x ε =
    map-tot-exists (λ _ → pr2) (exists-rational-approximate-above-ℝ x ε)
```

### Any real number can be approximated above to any positive rational precision `ε`

```agda
abstract opaque
  unfolding neighborhood-ℝ real-ℚ

  exists-rational-approximate-above-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    type-trunc-Prop (rational-approximate-above-ℝ x ε)
  exists-rational-approximate-above-ℝ {l} x ε⁺@(ε , _) =
    let
      open
        do-syntax-trunc-Prop
          ( trunc-Prop (rational-approximate-above-ℝ x ε⁺))
    in do
      ((p , q) , q<p+ε , p<x , x<q) ← is-arithmetically-located-ℝ x ε⁺
      intro-exists
        ( q)
        ( x<q ,
          ( λ r r+ε<q →
            le-lower-cut-ℝ
              ( x)
              ( reflects-le-left-add-ℚ ε r p
                ( transitive-le-ℚ
                  ( r +ℚ ε)
                  ( q)
                  ( p +ℚ ε)
                  ( q<p+ε)
                  ( map-inv-raise r+ε<q)))
              ( p<x)) ,
          ( λ r r+ε<x →
            map-raise
              ( le-lower-upper-cut-ℝ
                ( x)
                ( le-lower-cut-ℝ x (le-right-add-rational-ℚ⁺ r ε⁺) r+ε<x)
                ( x<q))))
```

### Any real number can be approximated to any rational precision `ε`

```agda
abstract
  exists-rational-approximate-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    type-trunc-Prop (rational-approximate-ℝ x ε)
  exists-rational-approximate-ℝ x ε =
    map-tot-exists (λ _ → pr2) (exists-rational-approximate-above-ℝ x ε)
```
