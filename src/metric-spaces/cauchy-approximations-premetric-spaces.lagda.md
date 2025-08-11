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
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a premetric space" Agda=cauchy-approximation-Premetric-Space}}
in a [premetric space](metric-spaces.premetric-spaces.md) is a map `f` from
[`ℚ⁺`](elementary-number-theory.positive-rational-numbers.md) to its carrier
type such that for all `(ε δ : ℚ⁺)`, `f ε` and `f δ` are in a
(`ε + δ`)-[neighborhood](metric-spaces.premetric-structures.md), i.e. the
distance between `f ε` and `f δ` is bounded by `ε + δ`.

## Definitions

### The property of being a Cauchy approximation in a premetric space

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

### The type of Cauchy approximations in a premetric space

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
    neighborhood-Premetric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Premetric-Space ε)
      ( map-cauchy-approximation-Premetric-Space δ)
  is-cauchy-map-cauchy-approximation-Premetric-Space = pr2 f
```

## Properties

### Short maps between premetric spaces preserve Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2)
  (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  (is-short-f : is-short-function-Premetric-Space A B f)
  (u : ℚ⁺ → type-Premetric-Space A)
  where

  preserves-is-cauchy-approximation-is-short-function-Premetric-Space :
    is-cauchy-approximation-Premetric-Space A u →
    is-cauchy-approximation-Premetric-Space B (f ∘ u)
  preserves-is-cauchy-approximation-is-short-function-Premetric-Space H ε δ =
    is-short-f (ε +ℚ⁺ δ) (u ε) (u δ) (H ε δ)
```

### Short maps between premetric spaces are functorial on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2)
  (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  where

  map-short-function-cauchy-approximation-Premetric-Space :
    cauchy-approximation-Premetric-Space A →
    cauchy-approximation-Premetric-Space B
  map-short-function-cauchy-approximation-Premetric-Space (u , H) =
    map-short-function-Premetric-Space A B f ∘ u ,
    preserves-is-cauchy-approximation-is-short-function-Premetric-Space
      ( A)
      ( B)
      ( map-short-function-Premetric-Space A B f)
      ( is-short-map-short-function-Premetric-Space A B f)
      ( u)
      ( H)

module _
  {l1 l2 : Level}
  (A : Premetric-Space l1 l2)
  where

  eq-id-map-short-function-cauchy-approximation-Premetric-Space :
    map-short-function-cauchy-approximation-Premetric-Space
      ( A)
      ( A)
      ( short-id-Premetric-Space A) ＝
    id
  eq-id-map-short-function-cauchy-approximation-Premetric-Space = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Premetric-Space l1a l2a)
  (B : Premetric-Space l1b l2b)
  (C : Premetric-Space l1c l2c)
  (g : short-function-Premetric-Space B C)
  (f : short-function-Premetric-Space A B)
  where

  eq-comp-map-short-function-cauchy-approximation-Premetric-Space :
    ( map-short-function-cauchy-approximation-Premetric-Space B C g ∘
      map-short-function-cauchy-approximation-Premetric-Space A B f) ＝
    ( map-short-function-cauchy-approximation-Premetric-Space A C
      (comp-short-function-Premetric-Space A B C g f))
  eq-comp-map-short-function-cauchy-approximation-Premetric-Space = refl
```

## References

Our definition of Cauchy approximation follows Definition 4.5.5 of
{{#cite Booij20PhD}} and Definition 11.2.10 of {{#cite UF13}}.

{{#bibliography}}
