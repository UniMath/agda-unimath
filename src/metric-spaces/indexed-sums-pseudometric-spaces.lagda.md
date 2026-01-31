# Indexed sums of pseudometric spaces

```agda
module metric-spaces.indexed-sums-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
```

</details>

## Idea

The
{{#concept "indexed sum" Disambiguation="of a type family of pseudometric spaces" Agda=indexed-sum-Pseudometric-Space}}
of a family `P` of [psudometric spaces](metric-spaces.pseudometric-spaces.md)
over a [set](foundation.sets.md) `A` is the pseudometric space with underlying
type `Σ A P` and the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
defined by:

The pair `(x , x')` is a `d`-neighbor of `(y , y')` if and only if `x` is
[equal](foundation.identity-types.md) to `y` and the
[transport](foundation.transport-along-identifications.md) of `x'` along this
identification is a `d`-neighbor of `y'` in `P y`.

For any `x : A` the embedding `P x → Σ A P` is an
[isometry](metric-spaces.isometries-pseudometric-spaces.md).

## Definitions

### Indexed sum of pseudometric spaces

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  where

  type-indexed-sum-Pseudometric-Space : UU (la ⊔ lp)
  type-indexed-sum-Pseudometric-Space =
    Σ (type-Set A) (type-Pseudometric-Space ∘ P)

  neighborhood-prop-indexed-sum-Pseudometric-Space :
    Rational-Neighborhood-Relation
      (la ⊔ lp')
      type-indexed-sum-Pseudometric-Space
  neighborhood-prop-indexed-sum-Pseudometric-Space d (x , x') (y , y') =
    Σ-Prop
      ( Id-Prop
        ( A)
        ( x)
        ( y))
      ( λ e →
        neighborhood-prop-Pseudometric-Space
        ( P y)
        ( d)
        ( tr (type-Pseudometric-Space ∘ P) e x')
        ( y'))

  is-reflexive-neighborhood-indexed-sum-Pseudometric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Pseudometric-Space
  is-reflexive-neighborhood-indexed-sum-Pseudometric-Space d (x , x') =
    (refl , refl-neighborhood-Pseudometric-Space (P x) d x')

  is-symmetric-neighborhood-indexed-sum-Pseudometric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Pseudometric-Space
  is-symmetric-neighborhood-indexed-sum-Pseudometric-Space
    d (x , x') (.x , x'') (refl , N) =
    (refl , symmetric-neighborhood-Pseudometric-Space (P x) d x' x'' N)

  is-triangular-neighborhood-indexed-Pseudometric-Space :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Pseudometric-Space
  is-triangular-neighborhood-indexed-Pseudometric-Space
    (x , xp) (.x , xp') (.x , xp'') d₁ d₂ (refl , K) (refl , H) =
    ( refl ,
      triangular-neighborhood-Pseudometric-Space
        ( P x)
        ( xp)
        ( xp')
        ( xp'')
        ( d₁)
        ( d₂)
        ( K)
        ( H))

  is-saturated-neighborhood-indexed-sum-Pseudometric-Space :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-indexed-sum-Pseudometric-Space
  is-saturated-neighborhood-indexed-sum-Pseudometric-Space
    d (x , x') (y , y') H = (x=y , lemma-neighborhood-Σ)
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
      neighborhood-Pseudometric-Space
        ( P y)
        ( d)
        ( tr (type-Pseudometric-Space ∘ P) x=y x')
        ( y')
    lemma-neighborhood-Σ =
      saturated-neighborhood-Pseudometric-Space
        ( P y)
        ( d)
        ( tr (type-Pseudometric-Space ∘ P) x=y x')
        ( y')
        ( λ δ →
          tr
            ( λ e →
              neighborhood-Pseudometric-Space
                (P y)
                (d +ℚ⁺ δ)
                ( tr (type-Pseudometric-Space ∘ P) e x')
                ( y'))
            ( all-eq-x=y δ)
            ( pr2 (H δ)))

  indexed-sum-Pseudometric-Space : Pseudometric-Space (la ⊔ lp) (la ⊔ lp')
  indexed-sum-Pseudometric-Space =
    ( type-indexed-sum-Pseudometric-Space ,
      neighborhood-prop-indexed-sum-Pseudometric-Space ,
      is-reflexive-neighborhood-indexed-sum-Pseudometric-Space ,
      is-symmetric-neighborhood-indexed-sum-Pseudometric-Space ,
      is-triangular-neighborhood-indexed-Pseudometric-Space ,
      is-saturated-neighborhood-indexed-sum-Pseudometric-Space)

  neighborhood-indexed-sum-Pseudometric-Space :
    ℚ⁺ → Relation (la ⊔ lp') type-indexed-sum-Pseudometric-Space
  neighborhood-indexed-sum-Pseudometric-Space =
    neighborhood-Pseudometric-Space
      indexed-sum-Pseudometric-Space

  base-point-indexed-sum-Pseudometric-Space :
    type-Pseudometric-Space indexed-sum-Pseudometric-Space → type-Set A
  base-point-indexed-sum-Pseudometric-Space = pr1

  fiber-point-indexed-sum-Pseudometric-Space :
    (x : type-indexed-sum-Pseudometric-Space) →
    type-Pseudometric-Space (P (base-point-indexed-sum-Pseudometric-Space x))
  fiber-point-indexed-sum-Pseudometric-Space = pr2

  map-emb-fiber-indexed-sum-Pseudometric-Space :
    (x : type-Set A) →
    type-Pseudometric-Space (P x) →
    type-indexed-sum-Pseudometric-Space
  map-emb-fiber-indexed-sum-Pseudometric-Space x px = (x , px)
```

## Properties

### Neighbors in the indexed same have equal base point

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (d : ℚ⁺)
  (x y : type-indexed-sum-Pseudometric-Space A P)
  (Nxy : neighborhood-indexed-sum-Pseudometric-Space A P d x y)
  where

  eq-base-neighbourhood-indexed-sum-Pseudometric-Space :
    base-point-indexed-sum-Pseudometric-Space A P x ＝
    base-point-indexed-sum-Pseudometric-Space A P y
  eq-base-neighbourhood-indexed-sum-Pseudometric-Space = pr1 Nxy
```

### Equality of base points induce isometries between fibers

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (x : type-Set A)
  where

  map-fiber-eq-base-indexed-sum-Pseudometric-Space :
    (y : type-Set A) → x ＝ y → map-Pseudometric-Space (P x) (P y)
  map-fiber-eq-base-indexed-sum-Pseudometric-Space y =
    tr (type-Pseudometric-Space ∘ P)

  is-isometry-map-fiber-eq-base-indexed-sum-Pseudometric-Space :
    (y : type-Set A) →
    (x=y : x ＝ y) →
    is-isometry-Pseudometric-Space
      ( P x)
      ( P y)
      ( map-fiber-eq-base-indexed-sum-Pseudometric-Space y x=y)
  is-isometry-map-fiber-eq-base-indexed-sum-Pseudometric-Space .x refl =
    is-isometry-id-Pseudometric-Space (P x)

  isometry-fiber-eq-base-indexed-sum-Pseudometric-Space :
    (y : type-Set A) →
    (x=y : x ＝ y) →
    isometry-Pseudometric-Space (P x) (P y)
  isometry-fiber-eq-base-indexed-sum-Pseudometric-Space y x=y =
    ( map-fiber-eq-base-indexed-sum-Pseudometric-Space y x=y ,
      is-isometry-map-fiber-eq-base-indexed-sum-Pseudometric-Space y x=y)
```

### Neighbors in the indexed sum are neighbors in fiber of the common base point

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (d : ℚ⁺)
  (x y : type-indexed-sum-Pseudometric-Space A P)
  (Nxy : neighborhood-indexed-sum-Pseudometric-Space A P d x y)
  where

  neighborhood-fiber-neighborhood-indexed-sum-Pseudometric-Space :
    neighborhood-Pseudometric-Space
      ( P (base-point-indexed-sum-Pseudometric-Space A P y))
      ( d)
      ( tr
        ( type-Pseudometric-Space ∘ P)
        ( eq-base-neighbourhood-indexed-sum-Pseudometric-Space A P d x y Nxy)
        ( fiber-point-indexed-sum-Pseudometric-Space A P x))
      ( fiber-point-indexed-sum-Pseudometric-Space A P y)
  neighborhood-fiber-neighborhood-indexed-sum-Pseudometric-Space = pr2 Nxy
```

### For any `x : A` the emebedding `P x → Σ A P` is an isometry

```agda
module _
  {la lp lp' : Level}
  (A : Set la)
  (P : type-Set A → Pseudometric-Space lp lp')
  (x : type-Set A)
  where

  is-short-map-map-emb-fiber-indexed-sum-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( P x)
      ( indexed-sum-Pseudometric-Space A P)
      ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x)
  is-short-map-map-emb-fiber-indexed-sum-Pseudometric-Space d px px' Nxx' =
    ( refl , Nxx')

  short-map-emb-fiber-indexed-sum-Pseudometric-Space :
    short-map-Pseudometric-Space (P x) (indexed-sum-Pseudometric-Space A P)
  short-map-emb-fiber-indexed-sum-Pseudometric-Space =
    ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x ,
      is-short-map-map-emb-fiber-indexed-sum-Pseudometric-Space)

  reflects-neighborhoods-emb-fiber-indexed-sum-Pseudometric-Space :
    (d : ℚ⁺) (px px' : type-Pseudometric-Space (P x)) →
    neighborhood-Pseudometric-Space
      ( indexed-sum-Pseudometric-Space A P)
      ( d)
      ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x px)
      ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x px') →
    neighborhood-Pseudometric-Space
      ( P x)
      ( d)
      ( px)
      ( px')
  reflects-neighborhoods-emb-fiber-indexed-sum-Pseudometric-Space
    d px px' (e , Nxx') =
    inv-tr
      ( λ e' →
        neighborhood-Pseudometric-Space
          ( P x)
          ( d)
          ( tr (type-Pseudometric-Space ∘ P) e' px)
          ( px'))
      ( axiom-K-is-set
        ( is-set-type-Set A)
        ( x)
        ( e))
      ( Nxx')

  is-isometry-map-emb-fiber-indexed-sum-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( P x)
      ( indexed-sum-Pseudometric-Space A P)
      ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x)
  is-isometry-map-emb-fiber-indexed-sum-Pseudometric-Space d px px' =
    ( is-short-map-map-emb-fiber-indexed-sum-Pseudometric-Space d px px' ,
      reflects-neighborhoods-emb-fiber-indexed-sum-Pseudometric-Space d px px')

  isometry-emb-fiber-indexed-Pseudometric-Space :
    isometry-Pseudometric-Space (P x) (indexed-sum-Pseudometric-Space A P)
  isometry-emb-fiber-indexed-Pseudometric-Space =
    ( map-emb-fiber-indexed-sum-Pseudometric-Space A P x ,
      is-isometry-map-emb-fiber-indexed-sum-Pseudometric-Space)
```
