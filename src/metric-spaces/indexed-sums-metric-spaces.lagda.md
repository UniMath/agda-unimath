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
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
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
open import metric-spaces.indexed-sums-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.locally-constant-maps-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
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
[locally constant](metric-spaces.locally-constant-maps-metric-spaces.md), and
for any `x : A` the embedding `P x → Σ A P` is an
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

  pseudometric-space-indexed-sum-Metric-Space :
    Pseudometric-Space (la ⊔ lp) (la ⊔ lp')
  pseudometric-space-indexed-sum-Metric-Space =
    indexed-sum-Pseudometric-Space A (pseudometric-Metric-Space ∘ P)

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
    ( pseudometric-space-indexed-sum-Metric-Space ,
      is-extensional-pseudometric-space-indexed-sum-Metric-Space)

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

  is-locally-constant-map-base-point-indexed-sum-Metric-Space :
    is-locally-constant-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( metric-space-discrete-metric-space-Set A)
      ( base-point-indexed-sum-Metric-Space A P)
  is-locally-constant-map-base-point-indexed-sum-Metric-Space x y =
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

  is-short-map-map-emb-fiber-indexed-sum-Metric-Space :
    is-short-map-Metric-Space
      ( P x)
      ( indexed-sum-Metric-Space A P)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x)
  is-short-map-map-emb-fiber-indexed-sum-Metric-Space d px px' Nxx' =
    ( refl , Nxx')

  short-map-emb-fiber-indexed-sum-Metric-Space :
    short-map-Metric-Space (P x) (indexed-sum-Metric-Space A P)
  short-map-emb-fiber-indexed-sum-Metric-Space =
    ( map-emb-fiber-indexed-sum-Metric-Space A P x ,
      is-short-map-map-emb-fiber-indexed-sum-Metric-Space)

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

  is-isometry-map-emb-fiber-indexed-sum-Metric-Space :
    is-isometry-Metric-Space
      ( P x)
      ( indexed-sum-Metric-Space A P)
      ( map-emb-fiber-indexed-sum-Metric-Space A P x)
  is-isometry-map-emb-fiber-indexed-sum-Metric-Space d px px' =
    ( is-short-map-map-emb-fiber-indexed-sum-Metric-Space d px px' ,
      reflects-neighborhoods-emb-fiber-indexed-sum-Metric-Space d px px')

  isometry-emb-fiber-indexed-sum-Metric-Space :
    isometry-Metric-Space (P x) (indexed-sum-Metric-Space A P)
  isometry-emb-fiber-indexed-sum-Metric-Space =
    ( map-emb-fiber-indexed-sum-Metric-Space A P x ,
      is-isometry-map-emb-fiber-indexed-sum-Metric-Space)
```

### Short maps from indexed sums are products of short maps

```agda
module _
  {la lp lp' lq lq' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  (Q : Metric-Space lq lq')
  where

  precomp-emb-fiber-short-map-indexed-sum-Metric-Space :
    short-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q) →
    (a : type-Set A) →
    short-map-Metric-Space (P a) Q
  precomp-emb-fiber-short-map-indexed-sum-Metric-Space f a =
    comp-short-map-Metric-Space
      ( P a)
      ( indexed-sum-Metric-Space A P)
      ( Q)
      ( f)
      ( short-map-emb-fiber-indexed-sum-Metric-Space A P a)

module _
  {la lp lp' lq lq' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  (Q : Metric-Space lq lq')
  (f : (a : type-Set A) → short-map-Metric-Space (P a) Q)
  where

  map-Π-short-map-fiber-indexed-sum-Metric-Space :
    map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q)
  map-Π-short-map-fiber-indexed-sum-Metric-Space (a , x) =
    map-short-map-Metric-Space (P a) Q (f a) x

  is-short-map-Π-short-map-fiber-indexed-sum-Metric-Space :
    is-short-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q)
      ( map-Π-short-map-fiber-indexed-sum-Metric-Space)
  is-short-map-Π-short-map-fiber-indexed-sum-Metric-Space
    d (a , x) (.a , y) (refl , Nxy) =
    is-short-map-short-map-Metric-Space (P a) Q (f a) d x y Nxy

  Π-short-map-fiber-indexed-sum-Metric-Space :
    short-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q)
  Π-short-map-fiber-indexed-sum-Metric-Space =
    ( map-Π-short-map-fiber-indexed-sum-Metric-Space ,
      is-short-map-Π-short-map-fiber-indexed-sum-Metric-Space)

module _
  {la lp lp' lq lq' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  (Q : Metric-Space lq lq')
  where abstract

  is-retraction-precomp-emb-fiber-short-map-indexed-sum-Metric-Space :
    Π-short-map-fiber-indexed-sum-Metric-Space A P Q ∘
    precomp-emb-fiber-short-map-indexed-sum-Metric-Space A P Q ~
    id
  is-retraction-precomp-emb-fiber-short-map-indexed-sum-Metric-Space f =
    eq-htpy-map-short-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q)
      ( Π-short-map-fiber-indexed-sum-Metric-Space A P Q
        ( precomp-emb-fiber-short-map-indexed-sum-Metric-Space A P Q f))
      ( f)
      ( refl-htpy)

  is-equiv-precomp-emb-fiber-short-map-indexed-sum-Metric-Space :
    is-equiv
      ( precomp-emb-fiber-short-map-indexed-sum-Metric-Space A P Q)
  is-equiv-precomp-emb-fiber-short-map-indexed-sum-Metric-Space =
    is-equiv-is-invertible
      ( Π-short-map-fiber-indexed-sum-Metric-Space A P Q)
      ( refl-htpy)
      ( is-retraction-precomp-emb-fiber-short-map-indexed-sum-Metric-Space)

module _
  {la lp lp' lq lq' : Level}
  (A : Set la)
  (P : type-Set A → Metric-Space lp lp')
  (Q : Metric-Space lq lq')
  where

  equiv-short-map-indexed-sum-Metric-Space :
    short-map-Metric-Space
      ( indexed-sum-Metric-Space A P)
      ( Q) ≃
    ((a : type-Set A) → short-map-Metric-Space (P a) Q)
  equiv-short-map-indexed-sum-Metric-Space =
    ( precomp-emb-fiber-short-map-indexed-sum-Metric-Space A P Q ,
      is-equiv-precomp-emb-fiber-short-map-indexed-sum-Metric-Space A P Q)
```
