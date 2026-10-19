# The complete metric space of Cauchy filters over pseudometric spaces

```agda
module metric-spaces.complete-metric-space-of-cauchy-filters-pseudometric-spaces where
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
open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
```

</details>

## Idea

In the
[metric space](metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces.md)
of [Cauchy filters](metric-spaces.cauchy-filters-pseudometric-spaces.md) on a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `M`, any
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
{{#concept "complete metric space of Cauchy filters" Disambiguation="on a pseudometric space" Agda=complete-metric-space-Cauchy-Filter-Pseudometric-Space}}
on the pseudometric space `M`.

## Definitions

### Cauchy approximations of Cauchy filters

```agda
module _
  { l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M))
  where

  map-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    ℚ⁺ → cauchy-filter-Pseudometric-Space l M
  map-cauchy-approximation-cauchy-filter-Pseudometric-Space =
    map-cauchy-approximation-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M)
      ( u)

  filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    ℚ⁺ → ℚ⁺ → type-Pseudometric-Space M → Prop l
  filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space d =
    neighborhood-subtype-cauchy-filter-Pseudometric-Space
      ( M)
      ( map-cauchy-approximation-cauchy-filter-Pseudometric-Space d)

  is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    ℚ⁺ → ℚ⁺ → type-Pseudometric-Space M → UU l
  is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space d =
    is-in-cauchy-filter-Pseudometric-Space
      ( M)
      ( map-cauchy-approximation-cauchy-filter-Pseudometric-Space d)

  neighborhood-is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    (ε δ α β : ℚ⁺) (x y : type-Pseudometric-Space M) →
    is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
      ( ε)
      ( α)
      ( x) →
    is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
      ( δ)
      ( β)
      ( y) →
    neighborhood-Pseudometric-Space M
      ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
      ( x)
      ( y)
  neighborhood-is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
    ε δ α β x y Ux Uy =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M)
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
  { l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M))
  where

  filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    Rational-Neighborhood-Subtype l (type-Pseudometric-Space M)
  filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space ε x =
    Π-Prop
      ( ℚ⁺)
      ( λ μ →
        ∃ ( ℚ⁺ × ℚ⁺)
          ( λ ( α , β) →
            le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ μ) ∧
            filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
              ( M)
              ( u)
              ( α)
              ( β)
              ( x)))

  is-proper-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    is-proper-Rational-Neighborhood-Subtype
      ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
  is-proper-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space ε =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( type-Pseudometric-Space M)
              ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
                ( ε)))
    in do
      ( η , η+η<ε) ← double-le-ℚ⁺ ε
      ( x , Rx) ←
        is-proper-cauchy-filter-Pseudometric-Space
          ( M)
          ( map-cauchy-approximation-cauchy-filter-Pseudometric-Space M u η)
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

  is-saturated-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    is-saturated-Rational-Neighborhood-Subtype
      ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
  is-saturated-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
    (ε , x) H μ =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ⁺ × ℚ⁺)
              ( λ ( α , β) →
                le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ μ) ∧
                filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
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

  neighborhood-is-in-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M) →
    is-bounded-neighborhood-subtype-Pseudometric-Space
      ( M)
      ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
      ( ε)
      ( δ)
      ( x)
      ( y)
  neighborhood-is-in-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
    ε δ x y (Rx , Ry) =
    saturated-neighborhood-Pseudometric-Space M
      ( ε +ℚ⁺ δ)
      ( x)
      ( y)
      ( lemma-saturate-neighborhood)
    where

    lemma-saturate-neighborhood :
      (μ : ℚ⁺) → neighborhood-Pseudometric-Space M (ε +ℚ⁺ δ +ℚ⁺ μ) x y
    lemma-saturate-neighborhood μ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Pseudometric-Space M (ε +ℚ⁺ δ +ℚ⁺ μ) x y)
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

        monotonic-neighborhood-Pseudometric-Space M
          ( x)
          ( y)
          ( βx +ℚ⁺ βy +ℚ⁺ (αx +ℚ⁺ αy))
          ( ε +ℚ⁺ δ +ℚ⁺ μ)
          ( le-αβ-εδμ)
          ( neighborhood-is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
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

  is-in-filter-neighborhood-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M) →
    is-enclosing-neighborhood-subtype-Pseudometric-Space
      ( M)
      ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
      ( ε)
      ( δ)
      ( x)
      ( y)
  is-in-filter-neighborhood-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
    ε δ x y (Rx , Nxy) μ =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ( ℚ⁺ × ℚ⁺)
              ( λ (α , β) →
                le-prop-ℚ⁺ (α +ℚ⁺ β) (ε +ℚ⁺ δ +ℚ⁺ μ) ∧
                filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
                  ( M)
                  ( u)
                  ( α)
                  ( β)
                  ( y)))
    in do
      ( (α , β) , (α+β<ε+μ , Rαβx)) ← Rx μ
      let
        Ry :
          is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
            ( M)
            ( u)
            ( α)
            ( β +ℚ⁺ δ)
            ( y)
        Ry =
          is-enclosing-cauchy-filter-Pseudometric-Space
            ( M)
            ( map-cauchy-approximation-cauchy-filter-Pseudometric-Space M u α)
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

  is-local-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    is-local-neighborhood-subtype-Pseudometric-Space
      ( M)
      ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
  is-local-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
    (ε , δ , x , y) =
    ( ( neighborhood-is-in-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
        ( ε)
        ( δ)
        ( x)
        ( y)) ,
      ( is-in-filter-neighborhood-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
        ( ε)
        ( δ)
        ( x)
        ( y)))

  lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    cauchy-filter-Pseudometric-Space l M
  lim-cauchy-approximation-cauchy-filter-Pseudometric-Space =
    ( filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space ,
      is-proper-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space ,
      is-saturated-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space ,
      is-local-filter-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)

  is-limit-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M)
      ( u)
      ( lim-cauchy-approximation-cauchy-filter-Pseudometric-Space)
  is-limit-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space
    ε δ (α , β , x , y) Rx Ly =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-Pseudometric-Space M
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

      monotonic-neighborhood-Pseudometric-Space M
        ( x)
        ( y)
        ( α +ℚ⁺ ν +ℚ⁺ (ε +ℚ⁺ η))
        ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
        ( le-ανεη-αβεδ)
        ( neighborhood-is-in-filter-map-cauchy-approximation-cauchy-filter-Pseudometric-Space
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
  { l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  where

  is-complete-metric-space-cauchy-filter-Pseudometric-Space :
    is-complete-Metric-Space
      ( metric-space-cauchy-filter-Pseudometric-Space l M)
  is-complete-metric-space-cauchy-filter-Pseudometric-Space u =
    ( lim-cauchy-approximation-cauchy-filter-Pseudometric-Space M u ,
      is-limit-lim-cauchy-approximation-cauchy-filter-Pseudometric-Space M u)
```

### The complete metric space of Cauchy filters

```agda
module _
  { l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  complete-metric-space-cauchy-filter-Pseudometric-Space :
    Complete-Metric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  complete-metric-space-cauchy-filter-Pseudometric-Space =
    ( metric-space-cauchy-filter-Pseudometric-Space l M ,
      is-complete-metric-space-cauchy-filter-Pseudometric-Space M)
```
