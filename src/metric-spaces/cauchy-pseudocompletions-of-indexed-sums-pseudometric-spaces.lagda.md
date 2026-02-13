# Cauchy pseudocompletions of indexed sums of pseudometric spaces

```agda
module metric-spaces.cauchy-pseudocompletions-of-indexed-sums-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.equality-of-pseudometric-spaces
open import metric-spaces.indexed-sums-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

Given a family of [peudometric spaces](metric-spaces.pseudometric-spaces.md)
`P : A → Pseudometric-Space` indexed by a [set](foundation-core.sets.md) `A`,
all
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in some fiber `P a` for `a : A` induce Cauchy approximations in the pseudometric
[indexed sum](metric-spaces.indexed-sums-pseudometric-spaces.md) `Σ A P`.

Conversely, for any Cauchy approximation `u` in `Σ A P`, there exists `aᵤ : A`
and a Cauchy approximation `uₐ` in `P aᵤ` such that `u ~ (aᵤ , uₐ)`. Thus, the
type of Cauchy approximations in an indexed sum of pseudometric spaces is
[equivalent](foundation-core.equivalences.md) to the indexed sum of the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md).

Moreover, this equivalence is an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) so it induces an
[equality](metric-spaces.equality-of-pseudometric-spaces.md) of pseudometric
spaces; therefore,
{{#concept "the Cauchy pseudocompletion of an indexed sum is the indexed sum of the Cauchy pseudocompletions" Disambiguation="in pseudometric spaces" Agda=eq-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space}}.

## Definitions

### Cauchy pseudocompletions of indexed sums of pseudometric spaces

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  cauchy-pseudocompletion-indexed-sum-Pseudometric-Space :
    Pseudometric-Space (la ⊔ lp ⊔ lp') (la ⊔ lp')
  cauchy-pseudocompletion-indexed-sum-Pseudometric-Space =
    cauchy-pseudocompletion-Pseudometric-Space
      ( indexed-sum-Pseudometric-Space A P)

  cauchy-approximation-indexed-sum-Pseudometric-Space : UU (la ⊔ lp ⊔ lp')
  cauchy-approximation-indexed-sum-Pseudometric-Space =
    type-Pseudometric-Space
      cauchy-pseudocompletion-indexed-sum-Pseudometric-Space

module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (u : cauchy-approximation-indexed-sum-Pseudometric-Space A P)
  where

  map-base-cauchy-approximation-indexed-sum-Pseudometric-Space :
    ℚ⁺ → type-Set A
  map-base-cauchy-approximation-indexed-sum-Pseudometric-Space d =
    base-point-indexed-sum-Pseudometric-Space A P
      ( map-cauchy-approximation-Pseudometric-Space
        ( indexed-sum-Pseudometric-Space A P)
        ( u)
        ( d))

  map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space :
    (d : ℚ⁺) →
    type-Pseudometric-Space
      ( P (map-base-cauchy-approximation-indexed-sum-Pseudometric-Space d))
  map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space d =
    fiber-point-indexed-sum-Pseudometric-Space A P
      ( map-cauchy-approximation-Pseudometric-Space
        ( indexed-sum-Pseudometric-Space A P)
        ( u)
        ( d))
```

### Indexed sums of Cauchy pseudocompletions of pseudometric spaces

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    Pseudometric-Space (la ⊔ lp ⊔ lp') (la ⊔ lp')
  indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    indexed-sum-Pseudometric-Space A
      ( cauchy-pseudocompletion-Pseudometric-Space ∘ P)

  type-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    UU (la ⊔ lp ⊔ lp')
  type-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    type-Pseudometric-Space
      indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
```

## Properties

### Cauchy approximations in a fiber induce Cauchy approximations in the indexed sum

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
  map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space (x , u) =
    map-cauchy-approximation-isometry-Pseudometric-Space
      ( P x)
      ( indexed-sum-Pseudometric-Space A P)
      ( isometry-emb-fiber-indexed-Pseudometric-Space A P x)
      ( u)
```

### Cauchy approximations in an indexed sum are Cauchy approximations in some fiber

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (u : cauchy-approximation-indexed-sum-Pseudometric-Space A P)
  where

  all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space :
    (ε δ : ℚ⁺) →
    map-base-cauchy-approximation-indexed-sum-Pseudometric-Space A P u ε ＝
    map-base-cauchy-approximation-indexed-sum-Pseudometric-Space A P u δ
  all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space ε δ =
    eq-base-neighbourhood-indexed-sum-Pseudometric-Space A P
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Pseudometric-Space
        ( indexed-sum-Pseudometric-Space A P)
        ( u)
        ( ε))
      ( map-cauchy-approximation-Pseudometric-Space
        ( indexed-sum-Pseudometric-Space A P)
        ( u)
        ( δ))
      ( is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
        ( indexed-sum-Pseudometric-Space A P)
        ( u)
        ( ε)
        ( δ))

  base-cauchy-approximation-indexed-sum-Pseudometric-Space : type-Set A
  base-cauchy-approximation-indexed-sum-Pseudometric-Space =
    map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
      ( A)
      ( P)
      ( u)
      ( one-ℚ⁺)

  contraction-base-cauchy-approximation-indexed-sum-Pseudometric-Space :
    (d : ℚ⁺) →
    map-base-cauchy-approximation-indexed-sum-Pseudometric-Space A P u d ＝
    base-cauchy-approximation-indexed-sum-Pseudometric-Space
  contraction-base-cauchy-approximation-indexed-sum-Pseudometric-Space d =
    all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space d one-ℚ⁺

  map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space :
    ℚ⁺ →
    type-Pseudometric-Space
      ( P base-cauchy-approximation-indexed-sum-Pseudometric-Space)
  map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
    d =
    tr
      ( type-Pseudometric-Space ∘ P)
      ( contraction-base-cauchy-approximation-indexed-sum-Pseudometric-Space d)
      ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space A P u d)

  is-cauchy-map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space :
    is-cauchy-approximation-Pseudometric-Space
      ( P base-cauchy-approximation-indexed-sum-Pseudometric-Space)
      ( map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space)
  is-cauchy-map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
    ε δ =
    tr
      ( λ z →
        neighborhood-Pseudometric-Space
          ( P base-cauchy-approximation-indexed-sum-Pseudometric-Space)
          ( ε +ℚ⁺ δ)
          ( z)
          ( map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( δ)))
      ( lemma)
      ( preserves-neighborhoods-map-isometry-Pseudometric-Space
        ( P
          ( map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( A)
            ( P)
            ( u)
            ( δ)))
        ( P base-cauchy-approximation-indexed-sum-Pseudometric-Space)
        ( isometry-fiber-eq-base-indexed-sum-Pseudometric-Space A P
          ( map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( A)
            ( P)
            ( u)
            ( δ))
          ( base-cauchy-approximation-indexed-sum-Pseudometric-Space)
          ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( δ)
            ( one-ℚ⁺)))
        ( ε +ℚ⁺ δ)
        ( tr
          ( type-Pseudometric-Space ∘ P)
          ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( ε)
            ( δ))
          ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( A)
            ( P)
            ( u)
            ( ε)))
        ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space A P u δ)
        ( neighborhood-fiber-neighborhood-indexed-sum-Pseudometric-Space
          ( A)
          ( P)
          ( ε +ℚ⁺ δ)
          ( map-cauchy-approximation-Pseudometric-Space
            ( indexed-sum-Pseudometric-Space A P)
            ( u)
            ( ε))
          ( map-cauchy-approximation-Pseudometric-Space
            ( indexed-sum-Pseudometric-Space A P)
            ( u)
            ( δ))
          ( is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
            ( indexed-sum-Pseudometric-Space A P)
            ( u)
            ( ε)
            ( δ))))
    where

    lemma :
      tr
        ( type-Pseudometric-Space ∘ P)
        ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
          ( δ)
          ( one-ℚ⁺))
        ( tr
          ( type-Pseudometric-Space ∘ P)
          ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( ε)
            ( δ))
          ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
            ( A)
            ( P)
            ( u)
            ( ε))) ＝
      map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
        ε
    lemma =
      ( comp-tr
        ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
          ( ε)
          ( δ))
        ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
          ( δ)
          ( one-ℚ⁺))
        ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
          ( A)
          ( P)
          ( u)
          ( ε))) ∙
      ( ap
        ( λ e →
          tr
            ( type-Pseudometric-Space ∘ P)
            ( e)
            ( map-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( A)
              ( P)
              ( u)
              ( ε)))
          ( is-set-has-uip
            ( is-set-type-Set A)
            ( map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( A)
              ( P)
              ( u)
              ( ε))
            ( base-cauchy-approximation-indexed-sum-Pseudometric-Space)
            ( ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( ε)
              ( δ)) ∙
              ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
                ( δ)
                ( one-ℚ⁺)))
            ( all-eq-map-base-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( ε)
              ( one-ℚ⁺))))

  cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space
      ( P base-cauchy-approximation-indexed-sum-Pseudometric-Space)
  cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
    =
    ( map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space ,
      is-cauchy-map-cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space)
```

### The map from the Cauchy pseudocompletion of an indexed sum to the indexed sum of Cauchy pseudocompletions

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  map-inv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
  map-inv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space u =
    ( base-cauchy-approximation-indexed-sum-Pseudometric-Space A P u ,
      cauchy-approximation-fiber-cauchy-approximation-indexed-sum-Pseudometric-Space
        ( A)
        ( P)
        ( u))
```

### The type of Cauchy approximations in an indexed sum is equivalent to the type of Cauchy approximmations in some fiber

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where abstract

  is-section-map-indexed-sum-pseudocompletion-Pseudometric-Space :
    ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ∘
      map-inv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P) ~
    id
  is-section-map-indexed-sum-pseudocompletion-Pseudometric-Space u =
    eq-htpy-cauchy-approximation-Pseudometric-Space
      ( indexed-sum-Pseudometric-Space A P)
      ( λ d →
        eq-pair-Σ
          ( inv
            ( contraction-base-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( A)
              ( P)
              ( u)
              ( d)))
          ( eq-transpose-tr
            ( contraction-base-cauchy-approximation-indexed-sum-Pseudometric-Space
              ( A)
              ( P)
              ( u)
              ( d))
            ( refl)))

  is-retraction-map-indexed-sum-pseudocompletion-Pseudometric-Space :
    ( map-inv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ∘
      map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P) ~
    id
  is-retraction-map-indexed-sum-pseudocompletion-Pseudometric-Space (b , u) =
    eq-pair-eq-fiber
      ( eq-htpy-cauchy-approximation-Pseudometric-Space
        ( P b)
        ( refl-htpy))

  is-equiv-map-indexed-sum-pseudocompletion-Pseudometric-Space :
    is-equiv
      ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
  is-equiv-map-indexed-sum-pseudocompletion-Pseudometric-Space =
    is-equiv-is-invertible
      ( map-inv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( is-section-map-indexed-sum-pseudocompletion-Pseudometric-Space)
      ( is-retraction-map-indexed-sum-pseudocompletion-Pseudometric-Space)

module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  equiv-type-indexed-sum-pseudocompletion-Pseudometric-Space :
    type-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ≃
    cauchy-approximation-indexed-sum-Pseudometric-Space A P
  equiv-type-indexed-sum-pseudocompletion-Pseudometric-Space =
    ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ,
      is-equiv-map-indexed-sum-pseudocompletion-Pseudometric-Space A P)
```

### The mapping from Cauchy approximations in fibers to Cauchy approximations in the indexed sum is short

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  abstract
    preserves-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
      is-short-map-Pseudometric-Space
        ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
        ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
        ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
    preserves-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
      d (x , u) (.x , v) (refl , Nuv) ε δ = (refl , Nuv ε δ)

  short-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
  short-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ,
      preserves-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space)
```

### The mapping from Cauchy approximations in fibers to Cauchy approximations in the indexed sum is an isometry

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where abstract

  map-neighborhood-fiber-eq-base-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    (x y : type-Set A) →
    (u : cauchy-approximation-Pseudometric-Space (P x))
    (v : cauchy-approximation-Pseudometric-Space (P y))
    (e : x ＝ y) →
    (d ε δ : ℚ⁺) →
    neighborhood-Pseudometric-Space
      ( P y)
      ( ε +ℚ⁺ δ +ℚ⁺ d)
      ( tr
        ( type-Pseudometric-Space ∘ P)
        ( e)
        ( map-cauchy-approximation-Pseudometric-Space
          ( P x)
          ( u)
        ( ε)))
      ( map-cauchy-approximation-Pseudometric-Space
        ( P y)
        ( v)
        ( δ)) →
    neighborhood-Pseudometric-Space
      ( P y)
      ( ε +ℚ⁺ δ +ℚ⁺ d)
      ( map-cauchy-approximation-Pseudometric-Space
        ( P y)
        ( tr
          ( cauchy-approximation-Pseudometric-Space ∘ P)
          ( e)
          ( u))
        ( ε))
      ( map-cauchy-approximation-Pseudometric-Space
        ( P y)
        ( v)
        ( δ))
  map-neighborhood-fiber-eq-base-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
    x .x u v refl d ε δ N = N

  reflects-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    (d : ℚ⁺) →
    (u v : type-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
      ( d)
      ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P u)
      ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P v) →
    neighborhood-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( d)
      ( u)
      ( v)
  reflects-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
    d (x , u) (y , v) Nuv = (x=y , neighborhood-fiber-x=y)
    where

    x=y : x ＝ y
    x=y = pr1 (Nuv one-ℚ⁺ one-ℚ⁺)

    neighborhood-fiber-x=y :
      (ε δ : ℚ⁺) →
      neighborhood-Pseudometric-Space
        ( P y)
        ( ε +ℚ⁺ δ +ℚ⁺ d)
        ( map-cauchy-approximation-Pseudometric-Space
          ( P y)
          ( tr
            ( cauchy-approximation-Pseudometric-Space ∘ P)
            ( x=y)
            ( u))
          ( ε))
        ( map-cauchy-approximation-Pseudometric-Space
          ( P y)
          ( v)
          ( δ))
    neighborhood-fiber-x=y ε δ =
      map-neighborhood-fiber-eq-base-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( x)
        ( y)
        ( u)
        ( v)
        ( x=y)
        ( d)
        ( ε)
        ( δ)
        ( tr
          ( λ e →
            neighborhood-Pseudometric-Space
              ( P y)
              ( ε +ℚ⁺ δ +ℚ⁺ d)
              ( tr
                ( type-Pseudometric-Space ∘ P)
                ( e)
                ( map-cauchy-approximation-Pseudometric-Space
                  ( P x)
                  ( u)
                  ( ε)))
              ( map-cauchy-approximation-Pseudometric-Space
                ( P y)
                ( v)
                ( δ)))
          ( is-set-has-uip
            ( is-set-type-Set A)
            ( x)
            ( y)
            ( pr1 (Nuv ε δ))
            ( x=y))
          ( pr2 (Nuv ε δ)))

  is-isometry-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
      ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
  is-isometry-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space d x y =
    ( ( preserves-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( A)
        ( P)
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( d)
        ( x)
        ( y)))
```

### The isometric equivalence between indexed sum of Cauchy pseudocompletions and pseudocompletions of indexed sums

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  isometry-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
  isometry-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ,
      is-isometry-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( A)
        ( P))

  isometric-equiv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    isometric-equiv-Pseudometric-Space
      ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
      ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P)
  isometric-equiv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    ( equiv-type-indexed-sum-pseudocompletion-Pseudometric-Space A P ,
      is-isometry-map-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( A)
        ( P))
```

### The Cauchy pseudocompletion of an indexed sum of pseudometric spaces is the indexed sum of the Cauchy pseudocompletions

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  eq-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space :
    indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P ＝
    cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P
  eq-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space =
    map-inv-equiv
      ( equiv-eq-isometric-equiv-Pseudometric-Space
        ( indexed-sum-cauchy-pseudocompletion-Pseudometric-Space A P)
        ( cauchy-pseudocompletion-indexed-sum-Pseudometric-Space A P))
      ( isometric-equiv-indexed-sum-cauchy-pseudocompletion-Pseudometric-Space
        ( A)
        ( P))
```
