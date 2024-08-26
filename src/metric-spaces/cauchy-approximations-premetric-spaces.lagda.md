# Cauchy approximations in premetric spaces

```agda
module metric-spaces.cauchy-approximations-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a premetric space" Agda=cauchy-approximation-Premetric-Space}}
in a [premetric space](metric-spaces.premetric-spaces.md) is a map `f` from
[`ℚ⁺`](elementary-number-theory.positive-rational-numbers.md) to its carrier
type such that `f ε` and `f δ` are
[(`ε + δ`)-close](metric-spaces.premetric-structures.md) for all `(ε δ : ℚ⁺)`.

This follows definition 4.5.5 of [Booij2020PhD] or Definition 11.2.10 of
{{#cite UF13}}.

## Definitions

### The property of being a cauchy approximation in a premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (f : ℚ⁺ → type-Premetric-Space A)
  where

  is-cauchy-approximation-prop-Premetric-Space : Prop l2
  is-cauchy-approximation-prop-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            structure-Premetric-Space A (ε +ℚ⁺ δ) (f ε) (f δ)))

  is-cauchy-approximation-Premetric-Space : UU l2
  is-cauchy-approximation-Premetric-Space =
    type-Prop is-cauchy-approximation-prop-Premetric-Space

  is-prop-is-cauchy-approximation-Premetric-Space :
    is-prop is-cauchy-approximation-Premetric-Space
  is-prop-is-cauchy-approximation-Premetric-Space =
    is-prop-type-Prop is-cauchy-approximation-prop-Premetric-Space
```

### The type of cauchy approximations in a premmetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  cauchy-approximation-Premetric-Space : UU (l1 ⊔ l2)
  cauchy-approximation-Premetric-Space =
    type-subtype (is-cauchy-approximation-prop-Premetric-Space A)

module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (f : cauchy-approximation-Premetric-Space A)
  where

  map-cauchy-approximation-Premetric-Space :
    ℚ⁺ → type-Premetric-Space A
  map-cauchy-approximation-Premetric-Space = pr1 f

  is-cauchy-map-cauchy-approximation-Premetric-Space :
    (ε δ : ℚ⁺) →
    is-close-Premetric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Premetric-Space ε)
      ( map-cauchy-approximation-Premetric-Space δ)
  is-cauchy-map-cauchy-approximation-Premetric-Space = pr2 f
```

## Properties

### Limits of a cauchy approximation in a premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (f : cauchy-approximation-Premetric-Space A)
  (l : type-Premetric-Space A)
  where

  is-limit-cauchy-approximation-prop-Premetric-Space : Prop l2
  is-limit-cauchy-approximation-prop-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            structure-Premetric-Space
              ( A)
              ( ε +ℚ⁺ δ)
              ( map-cauchy-approximation-Premetric-Space A f ε)
              ( l)))

  is-limit-cauchy-approximation-Premetric-Space : UU l2
  is-limit-cauchy-approximation-Premetric-Space =
    type-Prop is-limit-cauchy-approximation-prop-Premetric-Space

  is-prop-is-limit-cauchy-approximation-Premetric-Space :
    is-prop is-limit-cauchy-approximation-Premetric-Space
  is-prop-is-limit-cauchy-approximation-Premetric-Space =
    is-prop-type-Prop is-limit-cauchy-approximation-prop-Premetric-Space
```

## References

- [Booij2020PhD](https://etheses.bham.ac.uk/id/eprint/10411/7/Booij2020PhD.pdf)
  {{#bibliography}}
