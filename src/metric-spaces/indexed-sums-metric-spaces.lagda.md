# Indexed sums of metric spaces

```agda
module metric-spaces.indexed-sums-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.evaluation-functions
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.discrete-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.locally-constant-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

The
{{#concept "indexed sum" Disambiguation="of a type family of metric spaces" Agda=Σ-Metric-Space}}
of a type family `P` of [metric spaces](metric-spaces.metric-spaces.md) over a
[set](foundation.sets.md) `A` is the metric space with underlying type `Σ A P`
and the [neighborhood relation](metric-spaces.rational-neighborhoods.md) defined
as:

`(x , Px)` is `d`-neighbor of `(y , Py)` if and only if `x` is
[equal](foundation.identity-types.md) to `y` and the
[transport](foundation.transport-along-identifications.md) of `Px` along this
identification is a `d`-neighbor of `y` in `P y`.

The [projection](foundation.dependent-pair-types.md) on the first component is
[locally constant](metric-spaces.locally-constant-functions-metric-spaces.md),
and for any `x : A` the embedding `P x → Σ A P` is an
[isometry](metric-spaces.isometries-metric-spaces.md).

## Definitions

### Indexed sum of metric spaces

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  where

  type-Σ-Metric-Space : UU (la ⊔ lp)
  type-Σ-Metric-Space = Σ (type-Set A) (type-Metric-Space ∘ P)

  neighborhood-prop-Σ-Metric-Space :
    Rational-Neighborhood-Relation (la ⊔ lp') type-Σ-Metric-Space
  neighborhood-prop-Σ-Metric-Space d (x , Px) (y , Py) =
    Σ-Prop
      ( Id-Prop
        ( A)
        ( x)
        ( y))
      ( λ e →
        neighborhood-prop-Metric-Space
        ( P y)
        ( d)
        ( tr (type-Metric-Space ∘ P) e Px)
        ( Py))

  is-reflexive-neighborhood-Σ-Metric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-Σ-Metric-Space
  is-reflexive-neighborhood-Σ-Metric-Space d (x , Px) =
    (refl , refl-neighborhood-Metric-Space (P x) d Px)

  is-symmetric-neighborhood-Σ-Metric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-Σ-Metric-Space
  is-symmetric-neighborhood-Σ-Metric-Space d (x , Px) (.x , Px') (refl , Nxx') =
    (refl , symmetric-neighborhood-Metric-Space (P x) d Px Px' Nxx')

  is-triangular-neighborhood-Σ-Metric-Space :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-Σ-Metric-Space
  is-triangular-neighborhood-Σ-Metric-Space
    (x , Px) (.x , Px') (.x , Px'') d₁ d₂ (refl , K) (refl , H) =
    ( refl ,
      triangular-neighborhood-Metric-Space
      ( P x)
      ( Px)
      ( Px')
      ( Px'')
      ( d₁)
      ( d₂)
      ( K)
      ( H))

  is-saturated-neighborhood-Σ-Metric-Space :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-Σ-Metric-Space
  is-saturated-neighborhood-Σ-Metric-Space d (x , Px) (y , Py) H =
    ( x=y , lemma-neighborhood-Σ)
    where

    x=y : x ＝ y
    x=y = pr1 (H one-ℚ⁺)

    all-eq-x=y :
      (δ : ℚ⁺) → pr1 (H δ) ＝ x=y
    all-eq-x=y δ =
      is-set-has-uip
        ( is-set-type-Set A)
        ( x)
        ( y)
        ( pr1 (H δ))
        ( x=y)

    lemma-neighborhood-Σ :
      neighborhood-Metric-Space
        ( P y)
        ( d)
        ( tr (type-Metric-Space ∘ P) x=y Px)
        ( Py)
    lemma-neighborhood-Σ =
      saturated-neighborhood-Metric-Space
        ( P y)
        ( d)
        ( tr (type-Metric-Space ∘ P) x=y Px)
        ( Py)
        ( λ δ →
          tr
            ( λ e →
              neighborhood-Metric-Space
                (P y)
                (d +ℚ⁺ δ)
                ( tr (type-Metric-Space ∘ P) e Px)
                ( Py))
            ( all-eq-x=y δ)
            ( pr2 (H δ)))

  pseudometric-space-Σ-Metric-Space :
    Pseudometric-Space (la ⊔ lp) (la ⊔ lp')
  pseudometric-space-Σ-Metric-Space =
    ( type-Σ-Metric-Space ,
      neighborhood-prop-Σ-Metric-Space ,
      is-reflexive-neighborhood-Σ-Metric-Space ,
      is-symmetric-neighborhood-Σ-Metric-Space ,
      is-triangular-neighborhood-Σ-Metric-Space ,
      is-saturated-neighborhood-Σ-Metric-Space)

  is-tight-pseudometric-space-Σ-Metric-Space :
    is-tight-Pseudometric-Space pseudometric-space-Σ-Metric-Space
  is-tight-pseudometric-space-Σ-Metric-Space (x , Px) (y , Py) H =
    eq-pair-Σ
      ( x=y)
      ( eq-sim-Metric-Space
        ( P y)
        ( tr (type-Metric-Space ∘ P) x=y Px)
        ( Py)
        ( λ δ →
          tr
            ( λ e →
              neighborhood-Metric-Space
                ( P y)
                ( δ)
                ( tr (type-Metric-Space ∘ P) e Px)
                ( Py))
            ( all-eq-x=y δ)
            ( pr2 (H δ))))
    where

    x=y : x ＝ y
    x=y = pr1 (H one-ℚ⁺)

    all-eq-x=y :
      (δ : ℚ⁺) → pr1 (H δ) ＝ x=y
    all-eq-x=y δ =
      is-set-has-uip
        ( is-set-type-Set A)
        ( x)
        ( y)
        ( pr1 (H δ))
        ( x=y)

  is-extensional-pseudometric-space-Σ-Metric-Space :
    is-extensional-Pseudometric-Space pseudometric-space-Σ-Metric-Space
  is-extensional-pseudometric-space-Σ-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      pseudometric-space-Σ-Metric-Space
      is-tight-pseudometric-space-Σ-Metric-Space

  Σ-Metric-Space : Metric-Space (la ⊔ lp) (la ⊔ lp')
  Σ-Metric-Space =
    make-Metric-Space
      type-Σ-Metric-Space
      neighborhood-prop-Σ-Metric-Space
      is-reflexive-neighborhood-Σ-Metric-Space
      is-symmetric-neighborhood-Σ-Metric-Space
      is-triangular-neighborhood-Σ-Metric-Space
      is-saturated-neighborhood-Σ-Metric-Space
      is-extensional-pseudometric-space-Σ-Metric-Space

  base-point-Σ-Metric-Space :
    type-Metric-Space Σ-Metric-Space → type-Set A
  base-point-Σ-Metric-Space = pr1

  fiber-point-Σ-Metric-Space :
    (x : type-Σ-Metric-Space) →
    type-Metric-Space (P (base-point-Σ-Metric-Space x))
  fiber-point-Σ-Metric-Space = pr2

  map-emb-fiber-Σ-Metric-Space :
    (x : type-Set A) →
    type-Metric-Space (P x) →
    type-Σ-Metric-Space
  map-emb-fiber-Σ-Metric-Space x px = (x , px)
```

## Properties

### The projection on the first component of a indexed of metric spaces is locally constant

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  where

  is-locally-constant-base-point-Σ-Metric-Space :
    is-locally-constant-function-Metric-Space
      ( Σ-Metric-Space A P)
      ( metric-space-discrete-metric-space-Set A)
      ( base-point-Σ-Metric-Space A P)
  is-locally-constant-base-point-Σ-Metric-Space x y =
    elim-exists
      ( Id-Prop
        ( A)
        ( base-point-Σ-Metric-Space A P x)
        ( base-point-Σ-Metric-Space A P y))
      ( λ d Nxy → pr1 Nxy)
```

### For any `x : A` the emebedding `P x → Σ A P` is an isometry

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  (x : type-Set A)
  where

  is-short-emb-fiber-Σ-Metric-Space :
    is-short-function-Metric-Space
      ( P x)
      ( Σ-Metric-Space A P)
      ( map-emb-fiber-Σ-Metric-Space A P x)
  is-short-emb-fiber-Σ-Metric-Space d px px' Nxx' =
    ( refl , Nxx')

  short-emb-fiber-Σ-Metric-Space :
    short-function-Metric-Space (P x) (Σ-Metric-Space A P)
  short-emb-fiber-Σ-Metric-Space =
    ( map-emb-fiber-Σ-Metric-Space A P x) ,
    ( is-short-emb-fiber-Σ-Metric-Space)

  reflects-neighborhood-emb-fiber-Σ-Metric-Space :
    (d : ℚ⁺) (px px' : type-Metric-Space (P x)) →
    neighborhood-Metric-Space
      ( Σ-Metric-Space A P)
      ( d)
      ( map-emb-fiber-Σ-Metric-Space A P x px)
      ( map-emb-fiber-Σ-Metric-Space A P x px') →
    neighborhood-Metric-Space
      ( P x)
      ( d)
      ( px)
      ( px')
  reflects-neighborhood-emb-fiber-Σ-Metric-Space d px px' (e , Nxx') =
    inv-tr
      ( λ e' →
        neighborhood-Metric-Space
          ( P x)
          ( d)
          ( tr (type-Metric-Space ∘ P) e' px)
          ( px'))
      ( axiom-K-is-set
        ( is-set-type-Set A)
        ( x)
        ( e))
      ( Nxx')

  is-isometry-emb-fiber-Σ-Metric-Space :
    is-isometry-Metric-Space
      ( P x)
      ( Σ-Metric-Space A P)
      ( map-emb-fiber-Σ-Metric-Space A P x)
  is-isometry-emb-fiber-Σ-Metric-Space d px px' =
    ( is-short-emb-fiber-Σ-Metric-Space d px px' ,
      reflects-neighborhood-emb-fiber-Σ-Metric-Space d px px')

  isometry-emb-fiber-Σ-Metric-Space :
    isometry-Metric-Space (P x) (Σ-Metric-Space A P)
  isometry-emb-fiber-Σ-Metric-Space =
    ( map-emb-fiber-Σ-Metric-Space A P x ,
      is-isometry-emb-fiber-Σ-Metric-Space)
```
