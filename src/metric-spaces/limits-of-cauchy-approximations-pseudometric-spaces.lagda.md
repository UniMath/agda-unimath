# Limits of Cauchy approximations in pseudometric spaces

```agda
module metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
`f : ℚ⁺ → A` in a [pseudometric space](metric-spaces.pseudometric-spaces.md) `A`
has a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a pseudometric space" Agda=is-limit-cauchy-approximation-Pseudometric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`; more precisely, if `f ε` is in
a `ε + δ`-[neighborhood](metric-spaces.rational-neighborhood-relations.md) of
`x` for all `ε δ : ℚ⁺`.

## Definitions

### The property of having a limit in a pseudometric space

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (f : cauchy-approximation-Pseudometric-Space A)
  where

  is-limit-cauchy-approximation-prop-Pseudometric-Space :
    type-Pseudometric-Space A → Prop l2
  is-limit-cauchy-approximation-prop-Pseudometric-Space lim =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            neighborhood-prop-Pseudometric-Space
              ( A)
              ( ε +ℚ⁺ δ)
              ( map-cauchy-approximation-Pseudometric-Space A f ε)
              ( lim)))

  is-limit-cauchy-approximation-Pseudometric-Space :
    type-Pseudometric-Space A → UU l2
  is-limit-cauchy-approximation-Pseudometric-Space =
    type-Prop ∘ is-limit-cauchy-approximation-prop-Pseudometric-Space
```

## Properties

### Limits of a Cauchy approximations in a pseudometric space are similar

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (f : cauchy-approximation-Pseudometric-Space A)
  (x y : type-Pseudometric-Space A)
  where

  all-sim-is-limit-cauchy-approximation-Pseudometric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space A f x →
    is-limit-cauchy-approximation-Pseudometric-Space A f y →
    sim-Pseudometric-Space A x y
  all-sim-is-limit-cauchy-approximation-Pseudometric-Space lim-x lim-y d =
    let
      (ε , δ , ε+δ=d) = split-ℚ⁺ d
      θ = mediant-zero-min-ℚ⁺ ε δ
      θ<ε = le-left-mediant-zero-min-ℚ⁺ ε δ
      θ<δ = le-right-mediant-zero-min-ℚ⁺ ε δ
      ε' = le-diff-ℚ⁺ θ ε θ<ε
      δ' = le-diff-ℚ⁺ θ δ θ<δ
      fθ = map-cauchy-approximation-Pseudometric-Space A f θ

      Nεx : neighborhood-Pseudometric-Space A ε fθ x
      Nεx =
        tr
          ( is-upper-bound-dist-Pseudometric-Space A fθ x)
          ( right-diff-law-add-ℚ⁺ θ ε θ<ε)
          ( lim-x θ ε')

      Nδy : neighborhood-Pseudometric-Space A δ fθ y
      Nδy =
        tr
          ( is-upper-bound-dist-Pseudometric-Space A fθ y)
          ( right-diff-law-add-ℚ⁺ θ δ θ<δ)
          ( lim-y θ δ')

      Nxy : neighborhood-Pseudometric-Space A (ε +ℚ⁺ δ) x y
      Nxy =
        triangular-neighborhood-Pseudometric-Space
          ( A)
          ( x)
          ( fθ)
          ( y)
          ( ε)
          ( δ)
          ( Nδy)
          ( symmetric-neighborhood-Pseudometric-Space A ε fθ x Nεx)
    in
      tr
        ( is-upper-bound-dist-Pseudometric-Space A x y)
        ( ε+δ=d)
        ( Nxy)
```

### The value of a constant Cauchy approximation is its limit

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (x : type-Pseudometric-Space A)
  where

  is-limit-const-cauchy-approximation-Pseudometric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space
      ( A)
      ( const-cauchy-approximation-Pseudometric-Space A x)
      ( x)
  is-limit-const-cauchy-approximation-Pseudometric-Space ε δ =
    refl-neighborhood-Pseudometric-Space A _ x
```

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
