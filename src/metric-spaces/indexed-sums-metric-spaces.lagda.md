# Indexed sums of metric spaces

```agda
module metric-spaces.indexed-sums-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
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
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
```

</details>

## Idea

The
{{#concept "indexed sum" Disambiguation="of a type family of metric spaces" Agda=indexed-sum-Metric-Space}}
of a family `P` of [metric spaces](metric-spaces.metric-spaces.md) over a
[set](foundation.sets.md) `A` is the metric space with underlying type `Σ A P`
and the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
defined by:

The pair `(x , x')` is a `d`-neighbor of `(y , y')` if and only if `x` is
[equal](foundation.identity-types.md) to `y` and the
[transport](foundation.transport-along-identifications.md) of `x'` along this
identification is a `d`-neighbor of `y'` in `P y`.

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

  type-indexed-sum-Metric-Space : UU (la ⊔ lp)
  type-indexed-sum-Metric-Space = Σ (type-Set A) (type-Metric-Space ∘ P)

  neighborhood-prop-indexed-sum-Metric-Space :
    Rational-Neighborhood-Relation (la ⊔ lp') type-indexed-sum-Metric-Space
  neighborhood-prop-indexed-sum-Metric-Space d (x , x') (y , y') =
    Σ-Prop
      ( Id-Prop
        ( A)
        ( x)
        ( y))
      ( λ e →
        neighborhood-prop-Metric-Space
        ( P y)
        ( d)
        ( tr (type-Metric-Space ∘ P) e x')
        ( y'))

  is-reflexive-neighborhood-indexed-sum-Metric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Metric-Space
  is-reflexive-neighborhood-indexed-sum-Metric-Space d (x , x') =
    (refl , refl-neighborhood-Metric-Space (P x) d x')

  is-symmetric-neighborhood-indexed-sum-Metric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Metric-Space
  is-symmetric-neighborhood-indexed-sum-Metric-Space
    d (x , x') (.x , x'') (refl , N) =
    (refl , symmetric-neighborhood-Metric-Space (P x) d x' x'' N)

  is-triangular-neighborhood-indexed-Metric-Space :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Metric-Space
  is-triangular-neighborhood-indexed-Metric-Space
    (x , xp) (.x , xp') (.x , xp'') d₁ d₂ (refl , K) (refl , H) =
    ( refl ,
      triangular-neighborhood-Metric-Space
        ( P x)
        ( xp)
        ( xp')
        ( xp'')
        ( d₁)
        ( d₂)
        ( K)
        ( H))

  is-saturated-neighborhood-indexed-sum-Metric-Space :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Metric-Space
  is-saturated-neighborhood-indexed-sum-Metric-Space d (x , x') (y , y') H =
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
        ( tr (type-Metric-Space ∘ P) x=y x')
        ( y')
    lemma-neighborhood-Σ =
      saturated-neighborhood-Metric-Space
        ( P y)
        ( d)
        ( tr (type-Metric-Space ∘ P) x=y x')
        ( y')
        ( λ δ →
          tr
            ( λ e →
              neighborhood-Metric-Space
                (P y)
                (d +ℚ⁺ δ)
                ( tr (type-Metric-Space ∘ P) e x')
                ( y'))
            ( all-eq-x=y δ)
            ( pr2 (H δ)))

  pseudometric-space-indexed-sum-Metric-Space :
    Pseudometric-Space (la ⊔ lp) (la ⊔ lp')
  pseudometric-space-indexed-sum-Metric-Space =
    ( type-indexed-sum-Metric-Space ,
      neighborhood-prop-indexed-sum-Metric-Space ,
      is-reflexive-neighborhood-indexed-sum-Metric-Space ,
      is-symmetric-neighborhood-indexed-sum-Metric-Space ,
      is-triangular-neighborhood-indexed-Metric-Space ,
      is-saturated-neighborhood-indexed-sum-Metric-Space)

  is-tight-pseudometric-space-indexed-sum-Metric-Space :
    is-tight-Pseudometric-Space pseudometric-space-indexed-sum-Metric-Space
  is-tight-pseudometric-space-indexed-sum-Metric-Space (x , Px) (y , Py) H =
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

  is-extensional-pseudometric-space-indexed-sum-Metric-Space :
    is-extensional-Pseudometric-Space
      pseudometric-space-indexed-sum-Metric-Space
  is-extensional-pseudometric-space-indexed-sum-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      pseudometric-space-indexed-sum-Metric-Space
      is-tight-pseudometric-space-indexed-sum-Metric-Space

  indexed-sum-Metric-Space : Metric-Space (la ⊔ lp) (la ⊔ lp')
  indexed-sum-Metric-Space =
    make-Metric-Space
      ( type-indexed-sum-Metric-Space)
      ( neighborhood-prop-indexed-sum-Metric-Space)
      ( is-reflexive-neighborhood-indexed-sum-Metric-Space)
      ( is-symmetric-neighborhood-indexed-sum-Metric-Space)
      ( is-triangular-neighborhood-indexed-Metric-Space)
      ( is-saturated-neighborhood-indexed-sum-Metric-Space)
      ( is-extensional-pseudometric-space-indexed-sum-Metric-Space)

  base-point-indexed-sum-Metric-Space :
    type-Metric-Space indexed-sum-Metric-Space → type-Set A
  base-point-indexed-sum-Metric-Space = pr1

  fiber-point-indexed-sum-Metric-Space :
    (x : type-indexed-sum-Metric-Space) →
    type-Metric-Space (P (base-point-indexed-sum-Metric-Space x))
  fiber-point-indexed-sum-Metric-Space = pr2

  map-emb-fiber-indexed-sum-Metric-Space :
    (x : type-Set A) →
    type-Metric-Space (P x) →
    type-indexed-sum-Metric-Space
  map-emb-fiber-indexed-sum-Metric-Space x px = (x , px)
```

## Properties

### The projection on the first component of a indexed of metric spaces is locally constant

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  where

  is-locally-constant-base-point-indexed-sum-Metric-Space :
    is-locally-constant-function-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( metric-space-discrete-metric-space-Set A)
      ( base-point-indexed-sum-Metric-Space A P)
  is-locally-constant-base-point-indexed-sum-Metric-Space x y =
    elim-exists
      ( Id-Prop
        ( A)
        ( base-point-indexed-sum-Metric-Space A P x)
        ( base-point-indexed-sum-Metric-Space A P y))
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

  is-short-emb-fiber-indexed-sum-Metric-Space :
    is-short-function-Metric-Space
      ( P x)
      ( indexed-sum-Metric-Space A P)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x)
  is-short-emb-fiber-indexed-sum-Metric-Space d px px' Nxx' =
    ( refl , Nxx')

  short-emb-fiber-indexed-sum-Metric-Space :
    short-function-Metric-Space (P x) (indexed-sum-Metric-Space A P)
  short-emb-fiber-indexed-sum-Metric-Space =
    ( map-emb-fiber-indexed-sum-Metric-Space A P x ,
      is-short-emb-fiber-indexed-sum-Metric-Space)

  reflects-neighborhoods-emb-fiber-indexed-sum-Metric-Space :
    (d : ℚ⁺) (px px' : type-Metric-Space (P x)) →
    neighborhood-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( d)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x px)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x px') →
    neighborhood-Metric-Space
      ( P x)
      ( d)
      ( px)
      ( px')
  reflects-neighborhoods-emb-fiber-indexed-sum-Metric-Space
    d px px' (e , Nxx') =
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

  is-isometry-emb-fiber-indexed-sum-Metric-Space :
    is-isometry-Metric-Space
      ( P x)
      ( indexed-sum-Metric-Space A P)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x)
  is-isometry-emb-fiber-indexed-sum-Metric-Space d px px' =
    ( is-short-emb-fiber-indexed-sum-Metric-Space d px px' ,
      reflects-neighborhoods-emb-fiber-indexed-sum-Metric-Space d px px')

  isometry-emb-fiber-indexed-Metric-Space :
    isometry-Metric-Space (P x) (indexed-sum-Metric-Space A P)
  isometry-emb-fiber-indexed-Metric-Space =
    ( map-emb-fiber-indexed-sum-Metric-Space A P x ,
      is-isometry-emb-fiber-indexed-sum-Metric-Space)
```
