# Cauchy approximations in pseudometric spaces

```agda
module metric-spaces.cauchy-approximations-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a pseudometric space" Agda=is-cauchy-approximation-Pseudometric-Space}}
in a [pseudometric space](metric-spaces.pseudometric-spaces.md) `A` is a map `f`
from [`ℚ⁺`](elementary-number-theory.positive-rational-numbers.md) to the
carrier type of `A` such that for all
[positive rationals](elementary-number-theory.positive-rational-numbers.md) `ε`
and `δ`, `f ε` and `f δ` are in a
(`ε + δ`)-[neighborhood](metric-spaces.rational-neighborhood-relations.md),
i.e., the distance between `f ε` and `f δ` is bounded by `ε + δ`.

## Definitions

### Cauchy approximations in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-cauchy-approximation-prop-Pseudometric-Space :
    (ℚ⁺ → type-Pseudometric-Space A) → Prop l2
  is-cauchy-approximation-prop-Pseudometric-Space f =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            neighborhood-prop-Pseudometric-Space A (ε +ℚ⁺ δ) (f ε) (f δ)))

  is-cauchy-approximation-Pseudometric-Space :
    (ℚ⁺ → type-Pseudometric-Space A) → UU l2
  is-cauchy-approximation-Pseudometric-Space =
    type-Prop ∘ is-cauchy-approximation-prop-Pseudometric-Space

  cauchy-approximation-Pseudometric-Space : UU (l1 ⊔ l2)
  cauchy-approximation-Pseudometric-Space =
    type-subtype is-cauchy-approximation-prop-Pseudometric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (f : cauchy-approximation-Pseudometric-Space A)
  where

  map-cauchy-approximation-Pseudometric-Space :
    ℚ⁺ → type-Pseudometric-Space A
  map-cauchy-approximation-Pseudometric-Space = pr1 f

  is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Pseudometric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Pseudometric-Space ε)
      ( map-cauchy-approximation-Pseudometric-Space δ)
  is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space = pr2 f
```

## Properties

### Constant maps in pseudometric spaces are Cauchy approximations

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (x : type-Pseudometric-Space A)
  where

  const-cauchy-approximation-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space A
  pr1 const-cauchy-approximation-Pseudometric-Space _ = x
  pr2 const-cauchy-approximation-Pseudometric-Space ε δ =
    refl-neighborhood-Pseudometric-Space A (ε +ℚ⁺ δ) x
```

### Homotopic Cauchy approximations are equal

```agda
module _
  { l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  { f g : cauchy-approximation-Pseudometric-Space A}
  ( f~g :
    map-cauchy-approximation-Pseudometric-Space A f ~
    map-cauchy-approximation-Pseudometric-Space A g)
  where

  eq-htpy-cauchy-approximation-Pseudometric-Space : f ＝ g
  eq-htpy-cauchy-approximation-Pseudometric-Space =
    eq-type-subtype
      ( is-cauchy-approximation-prop-Pseudometric-Space A)
      ( eq-htpy f~g)
```

## References

Our definition of Cauchy approximation follows Definition 4.5.5 of
{{#cite Booij20PhD}} and Definition 11.2.10 of {{#cite UF13}}.

{{#bibliography}}
