# Cauchy approximations in the Cauchy pseudocompletion of a pseudometric space

```agda
{-# OPTIONS --lossy-unification #-}

module
  metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md)
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) have a
[limit](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md).

## Properties

### Any Cauchy approximation in the Cauchy pseudocompletion of a pseudometric space has a limit

```agda
module _
  { l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  ( U :
    cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M))
  where

  map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    ℚ⁺ → ℚ⁺ → type-Pseudometric-Space M
  map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space ε =
    map-cauchy-approximation-Pseudometric-Space M
      ( map-cauchy-approximation-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( U)
        ( ε))

  is-cauchy-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    (δ ε d₁ d₂ : ℚ⁺) →
    neighborhood-Pseudometric-Space
      ( M)
      ( d₁ +ℚ⁺ d₂ +ℚ⁺ (δ +ℚ⁺ ε))
      ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
        ( δ)
        ( d₁))
      ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
        ( ε)
        ( d₂))
  is-cauchy-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( U)

  map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    ℚ⁺ → type-Pseudometric-Space M
  map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space d =
    let
      (d₁ , d₂ , _) = split-ℚ⁺ d
    in
      map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space d₂ d₁

  abstract
    is-cauchy-map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
      is-cauchy-approximation-Pseudometric-Space
        ( M)
        ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space)
    is-cauchy-map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      δ ε =
      let
        (δ₁ , δ₂ , δ₁+δ₂=δ) = split-ℚ⁺ δ
        (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε

        lemma-δ+ε :
          ((δ₁ +ℚ⁺ ε₁) +ℚ⁺ (δ₂ +ℚ⁺ ε₂)) ＝ δ +ℚ⁺ ε
        lemma-δ+ε =
          ( interchange-law-add-add-ℚ⁺ δ₁ ε₁ δ₂ ε₂) ∙
          ( ap-binary add-ℚ⁺ δ₁+δ₂=δ ε₁+ε₂=ε)
      in
        tr
          ( is-upper-bound-dist-Pseudometric-Space
            ( M)
            ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( δ))
            ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( ε)))
          ( lemma-δ+ε)
          ( is-cauchy-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            _ _ _ _)

  lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space M
  lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space ,
      is-cauchy-map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space)

  abstract
    is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
      is-limit-cauchy-approximation-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( U)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space)
    is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      δ ε η θ =
      let
        (θ₁ , θ₂ , θ₁+θ₂=θ) = split-ℚ⁺ θ

        lemma-η+θ+δ :
          ((η +ℚ⁺ θ₁) +ℚ⁺ (δ +ℚ⁺ θ₂)) ＝ η +ℚ⁺ θ +ℚ⁺ δ
        lemma-η+θ+δ =
          ( interchange-law-add-add-ℚ⁺ η θ₁ δ θ₂) ∙
          ( ap
            ( add-ℚ⁺ (η +ℚ⁺ δ))
            ( θ₁+θ₂=θ)) ∙
          ( associative-add-ℚ⁺ η δ θ) ∙
          ( ap
            ( add-ℚ⁺ η)
            ( commutative-add-ℚ⁺ δ θ)) ∙
          ( inv (associative-add-ℚ⁺ η θ δ))

        lemma-lim :
          neighborhood-Pseudometric-Space M
            ( η +ℚ⁺ θ +ℚ⁺ δ)
            ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( δ)
              ( η))
            ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( θ₂)
              ( θ₁))
        lemma-lim =
          tr
            ( is-upper-bound-dist-Pseudometric-Space M
              ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( δ)
                ( η))
              ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( θ)))
            ( lemma-η+θ+δ)
            ( is-cauchy-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              _ _ _ _)
      in
        tr
          ( is-upper-bound-dist-Pseudometric-Space M
            ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( δ)
              ( η))
            ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( θ)))
          ( associative-add-ℚ⁺
            ( η +ℚ⁺ θ)
            ( δ)
            ( ε))
          ( monotonic-neighborhood-Pseudometric-Space M
            ( map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( δ)
              ( η))
            ( map-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( θ))
            ( η +ℚ⁺ θ +ℚ⁺ δ)
            ( η +ℚ⁺ θ +ℚ⁺ δ +ℚ⁺ ε)
            ( le-left-add-ℚ⁺ ( η +ℚ⁺ θ +ℚ⁺ δ) ε)
            ( lemma-lim))

  has-limit-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    Σ ( cauchy-approximation-Pseudometric-Space M)
      ( is-limit-cauchy-approximation-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( U))
  has-limit-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space =
    ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space ,
      is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space)
```

### Any Cauchy approximation in the pseudometric completion is similar to the constant Cauchy approximation of its limit

```agda
module _
  { l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M))
  where

  sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M))
      ( u)
      ( const-cauchy-approximation-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( u)))
  sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
    =
    sim-const-is-limit-cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( u)
      ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space M u)
      ( is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
        ( M)
        ( u))
```

### The map from a Cauchy approximation in the pseudometric completion to its limit is short

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-short-map-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
      is-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        ( ( const-cauchy-approximation-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space M)) ∘
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)))
    is-short-map-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      d u v =
      preserves-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        { u}
        { const-cauchy-approximation-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( u))}
        { v}
        { const-cauchy-approximation-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( v))}
        ( sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( u))
        ( sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( v))
        ( d)

    is-short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space :
      is-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space M)
    is-short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space
      d u v Nuv =
      reflects-neighborhoods-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( d)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( u))
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( v))
        ( is-short-map-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( d)
          ( u)
          ( v)
          ( Nuv))

  short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M))
      ( cauchy-pseudocompletion-Pseudometric-Space M)
  short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space =
    ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space M ,
      is-short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space)
```

### The map from a Cauchy approximation in the pseudometric completion to its limit is an isometry

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  abstract
    reflects-neighborhoods-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
      ( d : ℚ⁺) →
      ( u v :
        cauchy-approximation-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)) →
      neighborhood-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( d)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( u))
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( v)) →
      neighborhood-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        ( d)
        ( u)
        ( v)
    reflects-neighborhoods-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      d u v N-lim =
      reflects-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        { u}
        { const-cauchy-approximation-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( u))}
        { v}
        { const-cauchy-approximation-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( v))}
        ( sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( u))
        ( sim-const-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( M)
          ( v))
        ( d)
        ( preserves-neighborhoods-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M)
          ( d)
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( u))
          ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( M)
            ( v))
          ( N-lim))

    is-isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
      is-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space M))
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space M)
    is-isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      d x y =
      ( ( is-short-map-lim-cauchy-approximation-pseudocompletion-Pseudometric-Space
          ( M)
          ( d)
          ( x)
          ( y)) ,
        ( reflects-neighborhoods-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( d)
          ( x)
          ( y)))

  isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M))
      ( cauchy-pseudocompletion-Pseudometric-Space M)
  isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space =
    ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space M ,
      is-isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space)
```

### The image of a Cauchy approximation in the Cauchy pseudocompletion is convergent

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space M)
  where

  is-limit-map-cauchy-approximation-cauchy-pseudocompletion-Ppseudometric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( M)
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( short-map-unit-cauchy-pseudocompletion-Pseudometric-Space M)
        ( u))
      ( u)
  is-limit-map-cauchy-approximation-cauchy-pseudocompletion-Ppseudometric-Space
    ε δ α β =
    symmetric-neighborhood-Pseudometric-Space M
      ( (α +ℚ⁺ β) +ℚ⁺ (ε +ℚ⁺ δ))
      ( map-cauchy-approximation-Pseudometric-Space M u β)
      ( map-cauchy-approximation-Pseudometric-Space M u ε)
      ( monotonic-neighborhood-Pseudometric-Space M
        ( map-cauchy-approximation-Pseudometric-Space M u β)
        ( map-cauchy-approximation-Pseudometric-Space M u ε)
        ( β +ℚ⁺ ε)
        ( (α +ℚ⁺ β) +ℚ⁺ (ε +ℚ⁺ δ))
        ( preserves-strict-order-add-ℚ
          { rational-ℚ⁺ β}
          { rational-ℚ⁺ (α +ℚ⁺ β)}
          { rational-ℚ⁺ ε}
          { rational-ℚ⁺ (ε +ℚ⁺ δ)}
          ( le-right-add-ℚ⁺ α β)
          ( le-left-add-ℚ⁺ ε δ))
        ( is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
          ( M)
          ( u)
          ( β)
          ( ε)))

  sim-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M))
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( M)
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( short-map-unit-cauchy-pseudocompletion-Pseudometric-Space M)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( u))
  sim-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space =
    sim-const-is-limit-cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( M)
        ( cauchy-pseudocompletion-Pseudometric-Space M)
        ( short-map-unit-cauchy-pseudocompletion-Pseudometric-Space M)
        ( u))
      ( u)
      ( is-limit-map-cauchy-approximation-cauchy-pseudocompletion-Ppseudometric-Space)
```
