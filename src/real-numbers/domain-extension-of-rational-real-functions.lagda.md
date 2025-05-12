# Domain extension of rational real functions

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.domain-extension-of-rational-real-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A [real](real-numbers.dedekind-real-numbers.md) function `g : ℝ → ℝ` is an
{{#concept "extension" Disambiguation="of rational real functions"}} of a
[rational](elementary-number-theory.rational-numbers.md) function `f : ℚ → ℝ` if
`g ∘ real-ℚ ~ f`.

## Definitions

### The property of being an extension of a rational real function

```agda
module _
  {l : Level} (f : ℚ → ℝ l)
  {l' : Level} (g : ℝ l' → ℝ (l ⊔ l'))
  where

  is-extension-real-function-ℚ : UU (l ⊔ l')
  is-extension-real-function-ℚ =
    (q : ℚ) → sim-ℝ (g (raise-real-ℚ l' q)) (f q)

  opaque
    unfolding sim-ℝ

    is-prop-is-extension-real-function-ℚ :
      is-prop is-extension-real-function-ℚ
    is-prop-is-extension-real-function-ℚ =
      is-prop-Π
        ( λ q → is-prop-type-Prop (sim-prop-ℝ (g (raise-real-ℚ l' q)) (f q)))

  is-extension-prop-real-function-ℚ : Prop (l ⊔ l')
  is-extension-prop-real-function-ℚ =
    is-extension-real-function-ℚ ,
    is-prop-is-extension-real-function-ℚ
```

### The type of extensions of rational real functions

```agda
module _
  {l : Level} (f : ℚ → ℝ l) (l' : Level)
  where

  extension-real-function-ℚ : UU (lsuc l ⊔ lsuc l')
  extension-real-function-ℚ =
    type-subtype (is-extension-prop-real-function-ℚ f {l'})

  map-extension-real-function-ℚ :
    extension-real-function-ℚ → ℝ l' → ℝ (l ⊔ l')
  map-extension-real-function-ℚ = pr1

  is-extention-map-extension-real-function-ℚ :
    (H : extension-real-function-ℚ) →
    is-extension-real-function-ℚ f (map-extension-real-function-ℚ H)
  is-extention-map-extension-real-function-ℚ = pr2
```

## Properties

### If the extension of a rational real function is an isometry, so is the function

```agda
module _
  {l : Level} (f : ℚ → ℝ l)
  {l' : Level} (g : ℝ l' → ℝ (l ⊔ l'))
  (ext-fg : is-extension-real-function-ℚ f g)
  where

  is-isometry-is-isometry-is-extension-real-function-ℚ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℝ l')
      ( metric-space-leq-ℝ (l ⊔ l'))
      ( g) →
    is-isometry-Metric-Space
      ( metric-space-leq-ℚ)
      ( metric-space-leq-ℝ l)
      ( f)
  is-isometry-is-isometry-is-extension-real-function-ℚ I d x y =
    ( λ N →
      preserves-neighborhood-sim-ℝ
      ( d)
      ( g (raise-real-ℚ l' x))
      ( g (raise-real-ℚ l' y))
      ( f x)
      ( f y)
      ( ext-fg x)
      ( ext-fg y)
      ( forward-implication
        ( is-isometry-map-isometry-Metric-Space
          ( metric-space-leq-ℚ)
          ( metric-space-leq-ℝ (l ⊔ l'))
          ( comp-isometry-Metric-Space
            ( metric-space-leq-ℚ)
            ( metric-space-leq-ℝ l')
            ( metric-space-leq-ℝ (l ⊔ l'))
            ( g , I)
            ( isometry-metric-space-leq-raise-real-ℚ l'))
          ( d)
          ( x)
          ( y))
          ( N))) ,
    ( λ N →
      backward-implication
        ( is-isometry-map-isometry-Metric-Space
          ( metric-space-leq-ℚ)
          ( metric-space-leq-ℝ (l ⊔ l'))
          ( comp-isometry-Metric-Space
            ( metric-space-leq-ℚ)
            ( metric-space-leq-ℝ l')
            ( metric-space-leq-ℝ (l ⊔ l'))
            ( g , I)
            ( isometry-metric-space-leq-raise-real-ℚ l'))
          ( d)
          ( x)
          ( y))
          ( preserves-neighborhood-sim-ℝ
            ( d)
            ( f x)
            ( f y)
            ( g (raise-real-ℚ l' x))
            ( g (raise-real-ℚ l' y))
            ( symmetric-sim-ℝ (g (raise-real-ℚ l' x)) (f x) (ext-fg x))
            ( symmetric-sim-ℝ (g (raise-real-ℚ l' y)) (f y) (ext-fg y))
            ( N)))
```

### If the extension of a rational real function is short, so is the function

TODO

### If the extension of a rational real function is uniformly continuous so is the function

TODO

### Uniformly continuous extensions of rational real functions approximate the original function

```agda
module _
  {l : Level} (f : ℚ → ℝ l)
  {l' : Level} (g : ℝ l' → ℝ (l ⊔ l'))
  (ext-fg : is-extension-real-function-ℚ f g)
  where

  neighborhood-modulus-of-continuity-is-extension-real-function-ℚ :
    ( uc-modulus-g :
      modulus-of-uniform-continuity-map-Metric-Space
        ( metric-space-leq-ℝ l')
        ( metric-space-leq-ℝ (l ⊔ l'))
        ( g))
    ( x : ℝ l')
    ( y : ℚ)
    ( ε : ℚ⁺) →
    is-in-neighborhood-leq-ℝ
      ( l')
      ( pr1 uc-modulus-g ε)
      ( x)
      ( raise-real-ℚ l' y) →
    is-in-neighborhood-leq-ℝ
      (l ⊔ l')
      ( ε)
      ( g x)
      ( raise-ℝ l' (f y))
  neighborhood-modulus-of-continuity-is-extension-real-function-ℚ uc-g x y ε N =
    preserves-neighborhood-sim-ℝ
      ( ε)
      ( g x)
      ( g (raise-real-ℚ l' y))
      ( g x)
      ( raise-ℝ l' (f y))
      ( refl-sim-ℝ (g x))
      ( transitive-sim-ℝ
        ( g (raise-real-ℚ l' y))
        ( f y)
        ( raise-ℝ l' (f y))
        ( sim-raise-ℝ l' (f y))
        ( ext-fg y))
      ( ( pr2
          ( uc-g)
          ( x)
          ( ε)
          ( raise-real-ℚ l' y))
        ( N))
```

### Uniformly continuous extensions of rational real functions are unique

```agda
module _
  {l : Level} (f : ℚ → ℝ l)
  {l' : Level} (g h : ℝ l' → ℝ (l ⊔ l'))
  (ext-fg : is-extension-real-function-ℚ f g)
  (ext-fh : is-extension-real-function-ℚ f h)
  where

  sim-ev-modulus-of-uniform-continuity-is-extension-real-function-ℚ :
    modulus-of-uniform-continuity-map-Metric-Space
      ( metric-space-leq-ℝ l')
      ( metric-space-leq-ℝ (l ⊔ l'))
      ( g) →
    modulus-of-uniform-continuity-map-Metric-Space
      ( metric-space-leq-ℝ l')
      ( metric-space-leq-ℝ (l ⊔ l'))
      ( h) →
    (x : ℝ l') →
    (ε : ℚ⁺) →
    is-in-neighborhood-leq-ℝ (l ⊔ l') ε (g x) (h x)
  sim-ev-modulus-of-uniform-continuity-is-extension-real-function-ℚ
    uc-g uc-h x ε =
    tr
      ( is-upper-bound-dist-Metric-Space
        ( metric-space-leq-ℝ (l ⊔ l'))
        ( g x)
        ( h x))
      ( eq-add-split-ℚ⁺ ε)
      ( elim-exists
        ( premetric-leq-ℝ (l ⊔ l') (ε₁ +ℚ⁺ ε₂) (g x) (h x))
        ( λ y Nxy →
          is-triangular-premetric-leq-ℝ
            ( g x)
            ( raise-ℝ l' (f y))
            ( h x)
            ( ε₁)
            ( ε₂)
            ( is-symmetric-premetric-leq-ℝ
              ( ε₂)
              ( h x)
              ( raise-ℝ l' (f y))
            ( lemma-approx-h y Nxy))
            ( lemma-approx-g y Nxy))
        ( is-dense-real-ℚ x δ))
    where

    ε₁ ε₂ δ : ℚ⁺
    ε₁ = left-summand-split-ℚ⁺ ε
    ε₂ = right-summand-split-ℚ⁺ ε
    δ = mediant-zero-min-ℚ⁺ (pr1 uc-g ε₁) (pr1 uc-h ε₂)

    lemma-approx-g :
      (y : ℚ) →
      is-in-neighborhood-leq-ℝ l' δ x (raise-real-ℚ l' y) →
      is-in-neighborhood-leq-ℝ (l ⊔ l') ε₁ (g x) (raise-ℝ l' (f y))
    lemma-approx-g y Nxy =
      neighborhood-modulus-of-continuity-is-extension-real-function-ℚ
        ( f)
        ( g)
        ( ext-fg)
        ( uc-g)
        ( x)
        ( y)
        ( ε₁)
        ( is-monotonic-structure-Metric-Space
          ( metric-space-leq-ℝ l')
          ( x)
          ( raise-real-ℚ l' y)
          ( δ)
          ( pr1 uc-g ε₁)
          ( le-left-mediant-zero-min-ℚ⁺
            ( pr1 uc-g ε₁)
            ( pr1 uc-h ε₂))
          ( Nxy))

    lemma-approx-h :
      (y : ℚ) →
      is-in-neighborhood-leq-ℝ l' δ x (raise-real-ℚ l' y) →
      is-in-neighborhood-leq-ℝ (l ⊔ l') ε₂ (h x) (raise-ℝ l' (f y))
    lemma-approx-h y Nxy =
      neighborhood-modulus-of-continuity-is-extension-real-function-ℚ
        ( f)
        ( h)
        ( ext-fh)
        ( uc-h)
        ( x)
        ( y)
        ( ε₂)
        ( is-monotonic-structure-Metric-Space
          ( metric-space-leq-ℝ l')
          ( x)
          ( raise-real-ℚ l' y)
          ( δ)
          ( pr1 uc-h ε₂)
          ( le-right-mediant-zero-min-ℚ⁺
            ( pr1 uc-g ε₁)
            ( pr1 uc-h ε₂))
          ( Nxy))

module _
  { l : Level} (f : ℚ → ℝ l)
  { l' : Level} (g h : ℝ l' → ℝ (l ⊔ l'))
  ( ext-fg : is-extension-real-function-ℚ f g)
  ( ext-fh : is-extension-real-function-ℚ f h)
  ( uc-g :
    is-uniformly-continuous-map-Metric-Space
      (metric-space-leq-ℝ l')
      (metric-space-leq-ℝ (l ⊔ l'))
      ( g))
  ( uc-h :
    is-uniformly-continuous-map-Metric-Space
      (metric-space-leq-ℝ l')
      (metric-space-leq-ℝ (l ⊔ l'))
      ( h))
  where

  htpy-is-uniformly-continuous-real-extension-function-ℚ : g ~ h
  htpy-is-uniformly-continuous-real-extension-function-ℚ x =
    eq-indistinguishable-Metric-Space
      ( metric-space-leq-ℝ (l ⊔ l'))
      ( g x)
      ( h x)
      ( let
        open
          do-syntax-trunc-Prop
            ( is-indistinguishable-prop-Metric-Space
              ( metric-space-leq-ℝ (l ⊔ l'))
              ( g x)
              ( h x))
        in do
          modulus-uc-g ← uc-g
          modulus-uc-h ← uc-h
          sim-ev-modulus-of-uniform-continuity-is-extension-real-function-ℚ
            ( f)
            ( g)
            ( h)
            ( ext-fg)
            ( ext-fh)
            ( modulus-uc-g)
            ( modulus-uc-h)
            ( x))

  eq-is-uniformly-continuous-real-extension-function-ℚ : g ＝ h
  eq-is-uniformly-continuous-real-extension-function-ℚ =
    eq-htpy htpy-is-uniformly-continuous-real-extension-function-ℚ
```
