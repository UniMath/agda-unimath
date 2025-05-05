# Limits of Cauchy approximations in premetric spaces

```agda
module metric-spaces.limits-of-cauchy-approximations-premetric-spaces where
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-premetric-spaces
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

In a [premetric space](metric-spaces.premetric-spaces.md) `A`, an element `l` of
the carrier type of `A` is a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a premetric space" Agda=is-limit-cauchy-approximation-Premetric-Space}}
of a
[Cauchy approximation](metric-spaces.cauchy-approximations-premetric-spaces.md)
`f` in `A` if `f ε` is an
`(ε + δ)`-[neighbor](metric-spaces.premetric-structures.md) of `l` for all
[positive rationals](elementary-number-theory.positive-rational-numbers.md)
`(ε δ : ℚ⁺)`. This holds if and only if any `ε : ℚ⁺` is an upper bound on the
distance between `f δ` and `l` for all positive rational numbers `δ < ε`.

## Definitions

### Limits of a Cauchy approximation in a premetric space

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

  is-limit-prop-cauchy-approximation-Premetric-Space' : Prop l2
  is-limit-prop-cauchy-approximation-Premetric-Space' =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            hom-Prop
              ( le-prop-ℚ⁺ δ ε)
              ( structure-Premetric-Space
                ( A)
                ( ε)
                ( map-cauchy-approximation-Premetric-Space A f δ)
                ( l))))

  is-limit-cauchy-approximation-Premetric-Space' : UU l2
  is-limit-cauchy-approximation-Premetric-Space' =
    type-Prop is-limit-prop-cauchy-approximation-Premetric-Space'

  is-prop-is-limit-cauchy-approximation-Premetric-Space' :
    is-prop is-limit-cauchy-approximation-Premetric-Space'
  is-prop-is-limit-cauchy-approximation-Premetric-Space' =
    is-prop-type-Prop is-limit-prop-cauchy-approximation-Premetric-Space'
```

## Properties

### The two definitions of limits are equivalent

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (f : cauchy-approximation-Premetric-Space A)
  (l : type-Premetric-Space A)
  where

  is-limit'-is-limit-cauchy-approximation-Premetric-Space :
    is-limit-cauchy-approximation-Premetric-Space A f l →
    is-limit-cauchy-approximation-Premetric-Space' A f l
  is-limit'-is-limit-cauchy-approximation-Premetric-Space H ε δ I =
    tr
      ( is-upper-bound-dist-Premetric-Space
        ( A)
        ( map-cauchy-approximation-Premetric-Space A f δ)
        ( l))
      ( right-diff-law-add-ℚ⁺ δ ε I)
      ( H δ (le-diff-ℚ⁺ δ ε I))

  is-limit-is-limit'-cauchy-approximation-Premetric-Space :
    is-limit-cauchy-approximation-Premetric-Space' A f l →
    is-limit-cauchy-approximation-Premetric-Space A f l
  is-limit-is-limit'-cauchy-approximation-Premetric-Space H ε δ =
    H (ε +ℚ⁺ δ) ε (le-left-add-ℚ⁺ ε δ)
```

### Limits of Cauchy approximations in symmetric triangular premetric spaces are indistinguishable

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (is-symmetric-A : is-symmetric-Premetric (structure-Premetric-Space A))
  (is-triangular-A : is-triangular-Premetric (structure-Premetric-Space A))
  (f : cauchy-approximation-Premetric-Space A)
  {x y : type-Premetric-Space A}
  where

  is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space' :
    is-limit-cauchy-approximation-Premetric-Space' A f x →
    is-limit-cauchy-approximation-Premetric-Space' A f y →
    is-indistinguishable-Premetric-Space A x y
  is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space'
    lim-x lim-y d =
    tr
      ( is-upper-bound-dist-Premetric-Space A x y)
      ( eq-add-split-ℚ⁺ d)
      ( is-triangular-A
        ( x)
        ( map-cauchy-approximation-Premetric-Space
          ( A)
          ( f)
          ( mediant-zero-min-ℚ⁺
            ( left-summand-split-ℚ⁺ d)
            ( right-summand-split-ℚ⁺ d)))
        ( y)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( lim-y
          ( right-summand-split-ℚ⁺ d)
          ( mediant-zero-min-ℚ⁺
            ( left-summand-split-ℚ⁺ d)
            ( right-summand-split-ℚ⁺ d))
          ( le-right-mediant-zero-min-ℚ⁺
            ( left-summand-split-ℚ⁺ d)
            ( right-summand-split-ℚ⁺ d)))
        ( is-symmetric-A
          ( left-summand-split-ℚ⁺ d)
          ( map-cauchy-approximation-Premetric-Space
            ( A)
            ( f)
            ( mediant-zero-min-ℚ⁺
              ( left-summand-split-ℚ⁺ d)
              ( right-summand-split-ℚ⁺ d)))
          ( x)
          ( lim-x
            ( left-summand-split-ℚ⁺ d)
            ( mediant-zero-min-ℚ⁺
              ( left-summand-split-ℚ⁺ d)
              ( right-summand-split-ℚ⁺ d))
            ( le-left-mediant-zero-min-ℚ⁺
              ( left-summand-split-ℚ⁺ d)
              ( right-summand-split-ℚ⁺ d)))))

  is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space :
    is-limit-cauchy-approximation-Premetric-Space A f x →
    is-limit-cauchy-approximation-Premetric-Space A f y →
    is-indistinguishable-Premetric-Space A x y
  is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space
    lim-x lim-y =
    is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space'
      ( is-limit'-is-limit-cauchy-approximation-Premetric-Space A f x lim-x)
      ( is-limit'-is-limit-cauchy-approximation-Premetric-Space A f y lim-y)
```

### Limits of Cauchy approximations in a symmetric triangular extensional premetric space are equal

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  (S : is-symmetric-Premetric (structure-Premetric-Space A))
  (T : is-triangular-Premetric (structure-Premetric-Space A))
  (E : is-extensional-Premetric (structure-Premetric-Space A))
  (f : cauchy-approximation-Premetric-Space A)
  {x y : type-Premetric-Space A}
  where

  all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space' :
    (is-limit-cauchy-approximation-Premetric-Space' A f x) →
    (is-limit-cauchy-approximation-Premetric-Space' A f y) →
    (x ＝ y)
  all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space'
    I J =
    eq-indistinguishable-is-extensional-Premetric
      ( structure-Premetric-Space A)
      ( E)
      ( is-indistinguishable-is-limit-cauchy-approximation-triangular-symmetric-Premetric-Space'
        ( A)
        ( S)
        ( T)
        ( f)
        ( I)
        ( J))

  all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space :
    (is-limit-cauchy-approximation-Premetric-Space A f x) →
    (is-limit-cauchy-approximation-Premetric-Space A f y) →
    (x ＝ y)
  all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space
    I J =
    all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space'
      ( is-limit'-is-limit-cauchy-approximation-Premetric-Space A f x I)
      ( is-limit'-is-limit-cauchy-approximation-Premetric-Space A f y J)
```

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 from
{{#cite UF13}}.

{{#bibliography}}
