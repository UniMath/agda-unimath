# The complete metric space of Cauchy filters over metric spaces

```agda
module metric-spaces.complete-metric-space-of-cauchy-filters-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-cauchy-filters-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

In the
[metric space](metric-spaces.metric-space-of-cauchy-filters-metric-spaces.md) of
[Cauchy filters](metric-spaces.cauchy-filters-metric-spaces.md) on a
[metric space](metric-spaces.metric-spaces.md) `M`, any
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)

```text
  U : ℚ⁺ → ℚ⁺ → M → Prop l
```

[converges](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) to
the Cauchy filter given by

```text
  U∞ ε x = ∀ (μ : ℚ⁺) ∃ (α β : ℚ⁺) | (α + β < ε + μ) ∧ (U α β x)
```

Therefore, the metric space of Cauchy filters is
[complete](metric-spaces.complete-metric-spaces.md); this is the
{{#concept "complete metric space of Cauchy filters" Disambiguation="on a metric space" Agda=complete-metric-space-Cauchy-Filter-Metric-Space}}
on the metric space `M`.

## Definitions

### Cauchy approximations of Cauchy filters

```agda
module _
  { l1 l2 l : Level} (M : Metric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M))
  where

  map-cauchy-approximation-Cauchy-Filter-Metric-Space :
    ℚ⁺ → Cauchy-Filter-Metric-Space l M
  map-cauchy-approximation-Cauchy-Filter-Metric-Space =
    map-cauchy-approximation-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M)
      ( u)

  filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space :
    ℚ⁺ → ℚ⁺ → type-Metric-Space M → Prop l
  filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space d =
    ℚ⁺-subset-Cauchy-Filter-Metric-Space
      ( M)
      ( map-cauchy-approximation-Cauchy-Filter-Metric-Space d)

  is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space :
    ℚ⁺ → ℚ⁺ → type-Metric-Space M → UU l
  is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space d =
    is-in-filter-Cauchy-Filter-Metric-Space
      ( M)
      ( map-cauchy-approximation-Cauchy-Filter-Metric-Space d)

  neighborhood-is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space :
    (ε δ α β : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space ε α x →
    is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space δ β y →
    neighborhood-Metric-Space M
      ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
      ( x)
      ( y)
  neighborhood-is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
    ε δ α β x y Ux Uy =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M)
      ( u)
      ( ε)
      ( δ)
      ( α , β , x , y)
      ( Ux)
      ( Uy)
```

### Limits of Cauchy approximations of Cauchy filters

```agda
module _
  { l1 l2 l : Level} (M : Metric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M))
  where

  filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    ℚ⁺-subset-Metric-Space l M
  filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ε x =
    Π-Prop
      ( ℚ⁺)
      ( λ μ →
        ∃ ( ℚ⁺ × ℚ⁺)
          ( λ ( α , β) →
            le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ μ) ∧
            filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
              ( M)
              ( u)
              ( α)
              ( β)
              ( x)))

  is-total-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    is-total-ℚ⁺-subset-Metric-Space
      ( M)
      ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
  is-total-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ε =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( type-Metric-Space M)
              ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ε))
    in do
      ( η , η+η<ε) ← double-le-ℚ⁺ ε
      ( x , Rx) ←
        is-total-Cauchy-Filter-Metric-Space
          ( M)
          ( map-cauchy-approximation-Cauchy-Filter-Metric-Space M u η)
          ( η)

      intro-exists
        ( x)
        ( λ μ →
          intro-exists
            ( η , η)
            ( transitive-le-ℚ⁺
              ( η +ℚ⁺ η)
              ( ε)
              ( ε +ℚ⁺ μ)
              ( le-left-add-ℚ⁺ ε μ)
              ( η+η<ε) ,
              ( Rx)))

  is-saturated-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    is-saturated-ℚ⁺-subset-Metric-Space
      ( M)
      ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
  is-saturated-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
    ε x H μ =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ⁺ × ℚ⁺)
              ( λ ( α , β) →
                le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ μ) ∧
                filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
                  ( M)
                  ( u)
                  ( α)
                  ( β)
                  ( x)))
    in do
      ( (α , β) , (Hαβ , Rx)) ←
        H (left-summand-split-ℚ⁺ μ) (right-summand-split-ℚ⁺ μ)

      intro-exists
        ( α , β)
        ( ( tr
            ( le-ℚ⁺ (α +ℚ⁺ β))
            ( associative-add-ℚ⁺ _ _ _ ∙
              ap (add-ℚ⁺ ε) (eq-add-split-ℚ⁺ μ))
            ( Hαβ)) ,
          ( Rx))

  neighborhood-is-in-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    neighborhood-conjunction-ℚ⁺-subset-Metric-Space
      ( M)
      ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
      ( ε)
      ( δ)
      ( x)
      ( y)
  neighborhood-is-in-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
    ε δ x y (Rx , Ry) =
    saturated-neighborhood-Metric-Space M
      ( ε +ℚ⁺ δ)
      ( x)
      ( y)
      ( lemma-saturate-neighborhood)
    where

    lemma-saturate-neighborhood :
      (μ : ℚ⁺) → neighborhood-Metric-Space M (ε +ℚ⁺ δ +ℚ⁺ μ) x y
    lemma-saturate-neighborhood μ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Metric-Space M (ε +ℚ⁺ δ +ℚ⁺ μ) x y)
      in do
        ( η , η+η<μ) ← double-le-ℚ⁺ μ
        ( (αx , βx) , (le-αβx , Rαβx)) ← Rx η
        ( (αy , βy) , (le-αβy , Rαβy)) ← Ry η

        let
          le-αβ-εδμ : le-ℚ⁺ (βx +ℚ⁺ βy +ℚ⁺ (αx +ℚ⁺ αy)) (ε +ℚ⁺ δ +ℚ⁺ μ)
          le-αβ-εδμ =
            inv-tr
              ( λ z → le-ℚ⁺ z (ε +ℚ⁺ δ +ℚ⁺ μ))
              ( commutative-add-ℚ⁺ (βx +ℚ⁺ βy) (αx +ℚ⁺ αy) ∙
                interchange-law-add-add-ℚ⁺ αx αy βx βy)
              ( transitive-le-ℚ⁺
                ( (αx +ℚ⁺ βx) +ℚ⁺ (αy +ℚ⁺ βy))
                ( (ε +ℚ⁺ η) +ℚ⁺ (δ +ℚ⁺ η))
                ( ε +ℚ⁺ δ +ℚ⁺ μ)
                ( tr
                  ( λ z → le-ℚ⁺ z (ε +ℚ⁺ δ +ℚ⁺ μ))
                  ( interchange-law-add-add-ℚ⁺ ε δ η η)
                  ( preserves-le-right-add-ℚ⁺ (ε +ℚ⁺ δ) (η +ℚ⁺ η) μ η+η<μ))
                ( preserves-le-add-ℚ⁺
                  { αx +ℚ⁺ βx}
                  { ε +ℚ⁺ η}
                  { αy +ℚ⁺ βy}
                  { δ +ℚ⁺ η}
                  ( le-αβx)
                  ( le-αβy)))

        monotonic-neighborhood-Metric-Space M
          ( x)
          ( y)
          ( βx +ℚ⁺ βy +ℚ⁺ (αx +ℚ⁺ αy))
          ( ε +ℚ⁺ δ +ℚ⁺ μ)
          ( le-αβ-εδμ)
          ( neighborhood-is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
            ( M)
            ( u)
            ( αx)
            ( αy)
            ( βx)
            ( βy)
            ( x)
            ( y)
            ( Rαβx)
            ( Rαβy))

  is-in-filter-neighborhood-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space
      ( M)
      ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
      ( ε)
      ( δ)
      ( x)
      ( y)
  is-in-filter-neighborhood-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
    ε δ x y (Rx , Nxy) μ =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ⁺ × ℚ⁺)
              ( λ (α , β) →
                le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ δ +ℚ⁺ μ) ∧
                filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
                  ( M)
                  ( u)
                  ( α)
                  ( β)
                  ( y)))
    in do
      ( (α , β) , (α+β<ε+μ , Rαβx)) ← Rx μ
      let
        Ry :
          is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
            ( M)
            ( u)
            ( α)
            ( β +ℚ⁺ δ)
            ( y)
        Ry =
          is-in-filter-neighborhood-Cauchy-Filter-Metric-Space
            ( M)
            ( map-cauchy-approximation-Cauchy-Filter-Metric-Space M u α)
            ( β)
            ( δ)
            ( x)
            ( y)
            ( Rαβx)
            ( Nxy)

        le-αβδ-εδμ : le-ℚ⁺ (α +ℚ⁺ (β +ℚ⁺ δ)) (ε +ℚ⁺ δ +ℚ⁺ μ)
        le-αβδ-εδμ =
          binary-tr
            ( le-ℚ⁺)
            ( associative-add-ℚ⁺ α β δ)
            ( associative-add-ℚ⁺ ε μ δ ∙
              ap (add-ℚ⁺ ε) (commutative-add-ℚ⁺ μ δ) ∙
              inv (associative-add-ℚ⁺ ε δ μ))
            ( preserves-le-left-add-ℚ⁺
              ( δ)
              ( α +ℚ⁺ β)
              ( ε +ℚ⁺ μ)
              ( α+β<ε+μ))

      intro-exists
        ( α , β +ℚ⁺ δ)
        ( le-αβδ-εδμ , Ry)

  is-local-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    is-local-ℚ⁺-subset-Metric-Space
      ( M)
      ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
  is-local-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
    (ε , δ , x , y) =
    ( ( neighborhood-is-in-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
        ( ε)
        ( δ)
        ( x)
        ( y)) ,
      ( is-in-filter-neighborhood-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
        ( ε)
        ( δ)
        ( x)
        ( y)))

  lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    Cauchy-Filter-Metric-Space l M
  lim-cauchy-approximation-Cauchy-Filter-Metric-Space =
    ( filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ,
      is-total-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ,
      is-saturated-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space ,
      is-local-filter-lim-cauchy-approximation-Cauchy-Filter-Metric-Space)

  is-limit-lim-cauchy-approximation-Cauchy-Filter-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M)
      ( u)
      ( lim-cauchy-approximation-Cauchy-Filter-Metric-Space)
  is-limit-lim-cauchy-approximation-Cauchy-Filter-Metric-Space
    ε δ (α , β , x , y) Rx Ly =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-Metric-Space M
            ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
            ( x)
            ( y))
    in do
      ((η , ν) , (η+ν<β+δ , Ry)) ← Ly δ
      let
        le-ανεη-αβεδ : le-ℚ⁺ (α +ℚ⁺ ν +ℚ⁺ (ε +ℚ⁺ η)) ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
        le-ανεη-αβεδ =
          binary-tr
            ( le-ℚ⁺)
            ( interchange-law-add-add-ℚ⁺ α ε ν η)
            ( interchange-law-add-add-ℚ⁺ α ε β δ)
            ( preserves-le-right-add-ℚ⁺
              ( α +ℚ⁺ ε)
              ( ν +ℚ⁺ η)
              ( β +ℚ⁺ δ)
              ( tr (λ z → le-ℚ⁺ z (β +ℚ⁺ δ)) (commutative-add-ℚ⁺ η ν) η+ν<β+δ))

      monotonic-neighborhood-Metric-Space M
        ( x)
        ( y)
        ( α +ℚ⁺ ν +ℚ⁺ (ε +ℚ⁺ η))
        ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
        ( le-ανεη-αβεδ)
        ( neighborhood-is-in-filter-map-cauchy-approximation-Cauchy-Filter-Metric-Space
          ( M)
          ( u)
          ( ε)
          ( η)
          ( α)
          ( ν)
          ( x)
          ( y)
          ( Rx)
          ( Ry))
```

### The metric space of Cauchy filters is complete

```agda
module _
  { l1 l2 l : Level} (M : Metric-Space l1 l2)
  where

  is-complete-metric-space-Cauchy-Filter-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-Cauchy-Filter-Metric-Space l M)
  is-complete-metric-space-Cauchy-Filter-Metric-Space u =
    ( lim-cauchy-approximation-Cauchy-Filter-Metric-Space M u ,
      is-limit-lim-cauchy-approximation-Cauchy-Filter-Metric-Space M u)
```

### The complete metric space of Cauchy filters

```agda
module _
  { l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  complete-metric-space-Cauchy-Filter-Metric-Space :
    Complete-Metric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  complete-metric-space-Cauchy-Filter-Metric-Space =
    ( metric-space-Cauchy-Filter-Metric-Space l M ,
      is-complete-metric-space-Cauchy-Filter-Metric-Space M)
```
