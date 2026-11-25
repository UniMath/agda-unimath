# Cauchy filters on the Dedekind real numbers

```agda
module real-numbers.cauchy-filters-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-space-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.expansive-maps-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-filters-metric-spaces
open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
open import metric-spaces.short-maps-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.cauchy-filters-rational-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

Cauchy filters on Dedekind real numbers

## Definitions

### The complete metric space of Cauchy filters of Dedkind real numbers

```agda
module _
  (l1 l2 : Level)
  where

  complete-metric-space-cauchy-filter-ℝ :
    Complete-Metric-Space (lsuc l1 ⊔ lsuc l2) (lsuc l1 ⊔ l2)
  complete-metric-space-cauchy-filter-ℝ =
    complete-metric-space-cauchy-filter-Pseudometric-Space
      ( l2)
      ( pseudometric-space-ℝ l1)

  metric-space-cauchy-filter-ℝ : Metric-Space (lsuc l1 ⊔ lsuc l2) (lsuc l1 ⊔ l2)
  metric-space-cauchy-filter-ℝ =
    metric-space-Complete-Metric-Space
      complete-metric-space-cauchy-filter-ℝ

  cauchy-filter-ℝ : UU (lsuc l1 ⊔ lsuc l2)
  cauchy-filter-ℝ = type-Metric-Space metric-space-cauchy-filter-ℝ
```

### Components of Cauchy filters on the Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (V : cauchy-filter-ℝ l1 l2)
  where

  neighborhood-subtype-cauchy-filter-ℝ : ℚ⁺ → ℝ l1 → Prop l2
  neighborhood-subtype-cauchy-filter-ℝ =
    neighborhood-subtype-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-in-cauchy-filter-ℝ : ℚ⁺ → ℝ l1 → UU l2
  is-in-cauchy-filter-ℝ =
    is-in-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-proper-cauchy-filter-ℝ :
    (ε : ℚ⁺) → exists (ℝ l1) (neighborhood-subtype-cauchy-filter-ℝ ε)
  is-proper-cauchy-filter-ℝ =
    is-proper-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-saturated-cauchy-filter-ℝ :
    (ε : ℚ⁺) (p : ℝ l1) →
    ((μ : ℚ⁺) → is-in-cauchy-filter-ℝ (ε +ℚ⁺ μ) p) →
    is-in-cauchy-filter-ℝ ε p
  is-saturated-cauchy-filter-ℝ ε p =
    is-saturated-cauchy-filter-Metric-Space (metric-space-ℝ l1) V (ε , p)

  is-bounded-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℝ l1) →
    is-in-cauchy-filter-ℝ ε p →
    is-in-cauchy-filter-ℝ δ q →
    neighborhood-ℝ l1 (ε +ℚ⁺ δ) p q
  is-bounded-cauchy-filter-ℝ =
    is-bounded-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-enclosing-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℝ l1) →
    is-in-cauchy-filter-ℝ ε p →
    neighborhood-ℝ l1 δ p q →
    is-in-cauchy-filter-ℝ (ε +ℚ⁺ δ) q
  is-enclosing-cauchy-filter-ℝ =
    is-enclosing-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-monotonic-cauchy-filter-ℝ :
    (p : ℝ l1) (ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-ℝ ε p →
    is-in-cauchy-filter-ℝ δ p
  is-monotonic-cauchy-filter-ℝ =
    is-monotonic-cauchy-filter-Metric-Space (metric-space-ℝ l1) V
```

### The unit map of Cauchy filters on Dedekind real numbers

```agda
module _
  (l : Level)
  where

  isometry-unit-cauchy-filter-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
  isometry-unit-cauchy-filter-ℝ =
    isometry-unit-cauchy-filter-Pseudometric-Space
      ( pseudometric-space-ℝ l)

  map-unit-cauchy-filter-ℝ : ℝ l → cauchy-filter-ℝ l l
  map-unit-cauchy-filter-ℝ =
    map-isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
      ( isometry-unit-cauchy-filter-ℝ)

  is-isometry-map-unit-cauchy-filter-ℝ :
    is-isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
      ( map-unit-cauchy-filter-ℝ)
  is-isometry-map-unit-cauchy-filter-ℝ =
    is-isometry-map-isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
      ( isometry-unit-cauchy-filter-ℝ)
```

## Properties

### A Cauchy filter on the Dedekind real numbers induces a Cauchy filter in the rationals

```agda
module _
  {l1 l2 : Level} (V : cauchy-filter-ℝ l1 l2)
  where

  neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ :
    Rational-Neighborhood-Subtype l2 ℚ
  neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ε r =
    neighborhood-subtype-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( raise-real-ℚ l1 r)

  is-in-cauchy-filter-ℚ-cauchy-filter-ℝ :
    ℚ⁺ → ℚ → UU l2
  is-in-cauchy-filter-ℚ-cauchy-filter-ℝ =
    is-in-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ

  is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-proper-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ
  is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ ε =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ℚ (neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ε))
    in do
      (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
      (x , Vx) ← is-proper-cauchy-filter-ℝ V δ
      (p , Nxp) ← exists-rational-approximate-ℝ x δ

      intro-exists
        ( p)
        ( is-monotonic-cauchy-filter-ℝ
          ( V)
          ( raise-real-ℚ l1 p)
          ( δ +ℚ⁺ δ)
          ( ε)
          ( δ+δ<ε)
          ( is-enclosing-cauchy-filter-ℝ
            ( V)
            ( δ)
            ( δ)
            ( x)
            ( raise-real-ℚ l1 p)
            ( Vx)
            ( Nxp)))

  is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-saturated-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ
  is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ
    (ε , p) =
    is-saturated-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( raise-real-ℚ l1 p)

  is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-bounded-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ
    ε δ p q (Vp , Vq) =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l1)
      ( isometry-raise-real-ℚ l1)
      ( ε +ℚ⁺ δ)
      ( p)
      ( q)
      ( is-bounded-cauchy-filter-ℝ
        ( V)
        ( ε)
        ( δ)
        ( raise-real-ℚ l1 p)
        ( raise-real-ℚ l1 q)
        ( Vp)
        ( Vq))

  is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-enclosing-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ
    ε δ p q (Vp , Npq) =
    is-enclosing-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( δ)
      ( raise-real-ℚ l1 p)
      ( raise-real-ℚ l1 q)
      ( Vp)
      ( preserves-neighborhoods-map-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ l1)
        ( isometry-raise-real-ℚ l1)
        ( δ)
        ( p)
        ( q)
        ( Npq))

  is-local-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-local-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-local-cauchy-filter-ℚ-cauchy-filter-ℝ
    ( ε , δ , p , q) =
    ( is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ ε δ p q ,
      is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ ε δ p q)

  is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-cauchy-filter-Pseudometric-Space
      ( l2)
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ =
    ( is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-local-cauchy-filter-ℚ-cauchy-filter-ℝ)

  cauchy-filter-ℚ-cauchy-filter-ℝ : cauchy-filter-ℚ l2
  cauchy-filter-ℚ-cauchy-filter-ℝ =
    ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ)
```

### A Cauchy filter on the Dedekind real numbers induces a real number at the same level

```agda
module _
  {l1 l2 : Level} (V : cauchy-filter-ℝ l1 l2)
  where

  real-cauchy-filter-ℝ : ℝ l2
  real-cauchy-filter-ℝ =
    real-cauchy-filter-ℚ (cauchy-filter-ℚ-cauchy-filter-ℝ V)
```

### The map from Cauchy filters on real numbers to Cauchy filters on the rationals is an isometry

```agda
module _
  {l1 l2 : Level}
  where abstract

  is-short-map-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-short-map-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
      ( cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-short-map-cauchy-filter-ℚ-cauchy-filter-ℝ d x y Nxy (α , β , p , q) xp yq =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l1)
      ( isometry-raise-real-ℚ l1)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( p)
      ( q)
      ( Nxy (α , β , raise-real-ℚ l1 p , raise-real-ℚ l1 q) xp yq)

  is-expansive-map-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-expansive-map-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
      ( cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-expansive-map-cauchy-filter-ℚ-cauchy-filter-ℝ
    d u v Nuv (α , β , x , y) ux vy =
    is-saturated-neighborhood-ℝ
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( x)
      ( y)
      ( lemma-saturate-neighborhood)
    where

    lemma-saturate-neighborhood :
      (μ : ℚ⁺) → neighborhood-ℝ l1 (α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ μ) x y
    lemma-saturate-neighborhood μ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-ℝ l1 (α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ μ) x y)
      in do
        (ε , ε+ε<μ) ← double-le-ℚ⁺ μ
        (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
        (p , up) ← is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ u δ
        (q , vq) ← is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ v δ

        let
          Nxp : neighborhood-ℝ l1 (α +ℚ⁺ δ) x (raise-real-ℚ l1 p)
          Nxp =
            is-bounded-cauchy-filter-ℝ
              ( u)
              ( α)
              ( δ)
              ( x)
              ( raise-real-ℚ l1 p)
              ( ux)
              ( up)

          Nyq : neighborhood-ℝ l1 (β +ℚ⁺ δ) y (raise-real-ℚ l1 q)
          Nyq =
            is-bounded-cauchy-filter-ℝ
              ( v)
              ( β)
              ( δ)
              ( y)
              ( raise-real-ℚ l1 q)
              ( vy)
              ( vq)

          Nxy :
            neighborhood-ℝ l1 (α +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ (β +ℚ⁺ δ)) x y
          Nxy =
            is-triangular-neighborhood-ℝ
              ( x)
              ( raise-real-ℚ l1 q)
              ( y)
              ( α +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d))
              ( β +ℚ⁺ δ)
              ( is-symmetric-neighborhood-ℝ
                ( β +ℚ⁺ δ)
                ( y)
                ( raise-real-ℚ l1 q)
                ( Nyq))
              ( is-triangular-neighborhood-ℝ
                ( x)
                ( raise-real-ℚ l1 p)
                ( raise-real-ℚ l1 q)
                ( α +ℚ⁺ δ)
                ( δ +ℚ⁺ δ +ℚ⁺ d)
                ( preserves-neighborhoods-map-isometry-Metric-Space
                  ( metric-space-ℚ)
                  ( metric-space-ℝ l1)
                  ( isometry-raise-real-ℚ l1)
                  ( δ +ℚ⁺ δ +ℚ⁺ d)
                  ( p)
                  ( q)
                  ( Nuv (δ , δ , p , q) up vq))
                ( Nxp))

          interchange-δd :
            δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ) ＝ d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
          interchange-δd =
            commutative-add-ℚ⁺ δ (δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ) ∙
            associative-add-ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) δ δ ∙
            associative-add-ℚ⁺ (δ +ℚ⁺ δ) d (δ +ℚ⁺ δ) ∙
            ap (add-ℚ⁺ (δ +ℚ⁺ δ)) (commutative-add-ℚ⁺ d (δ +ℚ⁺ δ)) ∙
            inv (associative-add-ℚ⁺ (δ +ℚ⁺ δ) (δ +ℚ⁺ δ) d) ∙
            commutative-add-ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) d

          interchange-αβδd :
            ( α +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ (β +ℚ⁺ δ)) ＝
            ( α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)))
          interchange-αβδd =
            equational-reasoning
            α +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ (β +ℚ⁺ δ)
            ＝ α +ℚ⁺ δ +ℚ⁺ β +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ)
              by
                interchange-law-add-add-ℚ⁺
                  ( α +ℚ⁺ δ)
                  ( δ +ℚ⁺ δ +ℚ⁺ d)
                  ( β)
                  ( δ)
            ＝ (α +ℚ⁺ δ) +ℚ⁺ (β +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ))
              by
                associative-add-ℚ⁺
                  ( α +ℚ⁺ δ)
                  ( β)
                  ( δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ)
            ＝ (α +ℚ⁺ β) +ℚ⁺ (δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ))
              by
                interchange-law-add-add-ℚ⁺
                  ( α)
                  ( δ)
                  ( β)
                  ( δ +ℚ⁺ δ +ℚ⁺ d +ℚ⁺ δ)
            ＝ (α +ℚ⁺ β) +ℚ⁺ (d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)))
              by
                ap
                  ( add-ℚ⁺ (α +ℚ⁺ β))
                  ( interchange-δd)
            ＝ α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
              by
                inv
                  ( associative-add-ℚ⁺
                    ( α +ℚ⁺ β)
                    ( d)
                    ( δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)))

          le-δμ : le-ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ)) μ
          le-δμ =
            transitive-le-ℚ⁺
              ( δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
              ( ε +ℚ⁺ ε)
              ( μ)
              ( ε+ε<μ)
              ( preserves-le-add-ℚ⁺
                { δ +ℚ⁺ δ}
                { ε}
                { δ +ℚ⁺ δ}
                { ε}
                ( δ+δ<ε)
                ( δ+δ<ε))

        monotonic-neighborhood-ℝ
          ( x)
          ( y)
          ( α +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ +ℚ⁺ d) +ℚ⁺ (β +ℚ⁺ δ))
          ( α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ μ)
          ( inv-tr
            ( λ z → le-ℚ⁺ z (α +ℚ⁺ β +ℚ⁺ d +ℚ⁺ μ))
            ( interchange-αβδd)
            ( preserves-le-right-add-ℚ⁺
              ( α +ℚ⁺ β +ℚ⁺ d)
              ( δ +ℚ⁺ δ +ℚ⁺ (δ +ℚ⁺ δ))
              ( μ)
              ( le-δμ)))
          ( Nxy)

  is-isometry-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-isometry-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
      ( cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-isometry-cauchy-filter-ℚ-cauchy-filter-ℝ =
    is-isometry-is-expansive-map-is-short-map-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
      ( cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( is-short-map-cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( is-expansive-map-cauchy-filter-ℚ-cauchy-filter-ℝ)
```

### The isometry from Cauchy filters on real numbers to Cauchy filters on rational numbers

```agda
module _
  {l1 l2 : Level}
  where

  isometry-cauchy-filter-ℚ-cauchy-filter-ℝ :
    isometry-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
  isometry-cauchy-filter-ℚ-cauchy-filter-ℝ =
    ( cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-isometry-cauchy-filter-ℚ-cauchy-filter-ℝ)
```

### The isometry from Cauchy filters on real numbers to Dedekind real numbers

```agda
module _
  {l1 l2 : Level}
  where

  isometry-real-cauchy-filter-ℝ :
    isometry-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-ℝ l2)
  isometry-real-cauchy-filter-ℝ =
    comp-isometry-Metric-Space
      ( metric-space-cauchy-filter-ℝ l1 l2)
      ( metric-space-cauchy-filter-ℚ l2)
      ( metric-space-ℝ l2)
      ( isometry-real-cauchy-filter-ℚ)
      ( isometry-cauchy-filter-ℚ-cauchy-filter-ℝ)
```

### The real number induced by a Cauchy filter of real numbers is its limit

```agda
module _
  {l : Level} (V : cauchy-filter-ℝ l l)
  where abstract

  is-limit-real-cauchy-filter-ℝ :
    is-limit-cauchy-filter-Metric-Space
      ( metric-space-ℝ l)
      ( V)
      ( real-cauchy-filter-ℝ V)
  is-limit-real-cauchy-filter-ℝ ε =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-subtype-cauchy-filter-ℝ
            ( V)
            ( ε)
            ( real-cauchy-filter-ℝ V))
    in do
      (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
      (q , Vq) ← is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ V δ

      is-monotonic-cauchy-filter-ℝ
        ( V)
        ( real-cauchy-filter-ℝ V)
        ( δ +ℚ⁺ δ)
        ( ε)
        ( δ+δ<ε)
        ( is-enclosing-cauchy-filter-ℝ
          ( V)
          ( δ)
          ( δ)
          ( raise-real-ℚ l q)
          ( real-cauchy-filter-ℝ V)
          ( Vq)
          ( is-symmetric-neighborhood-ℝ
            ( δ)
            ( real-cauchy-filter-ℝ V)
            ( raise-real-ℚ l q)
            ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ
              ( cauchy-filter-ℚ-cauchy-filter-ℝ V)
              ( δ)
              ( q)
              ( Vq))))
```

### The unit map of Cauchy filters on real numbers is an equivalence

```agda
module _
  {l : Level}
  where abstract

  is-section-real-cauchy-filter-ℝ :
    real-cauchy-filter-ℝ ∘ map-unit-cauchy-filter-ℝ l ~ id
  is-section-real-cauchy-filter-ℝ x =
    all-eq-is-limit-cauchy-filter-Metric-Space
      ( metric-space-ℝ l)
      ( map-unit-cauchy-filter-ℝ l x)
      ( real-cauchy-filter-ℝ (map-unit-cauchy-filter-ℝ l x))
      ( x)
      ( is-limit-real-cauchy-filter-ℝ (map-unit-cauchy-filter-ℝ l x))
      ( is-limit-map-unit-cauchy-filter-Metric-Space (metric-space-ℝ l) x)

  is-equiv-map-unit-cauchy-filter-ℝ :
    is-equiv (map-unit-cauchy-filter-ℝ l)
  is-equiv-map-unit-cauchy-filter-ℝ =
    is-equiv-is-retraction-isometry-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
      ( isometry-unit-cauchy-filter-ℝ l)
      ( isometry-real-cauchy-filter-ℝ)
      ( is-section-real-cauchy-filter-ℝ)
```

### Dedekind real numbers are isometrically equivalent to Cauchy filters on themselves

```agda
module _
  {l : Level}
  where

  equiv-unit-cauchy-filter-ℝ : ℝ l ≃ cauchy-filter-ℝ l l
  equiv-unit-cauchy-filter-ℝ =
    ( map-unit-cauchy-filter-ℝ l , is-equiv-map-unit-cauchy-filter-ℝ)

  isometric-equiv-unit-cauchy-filter-ℝ :
    isometric-equiv-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-cauchy-filter-ℝ l l)
  isometric-equiv-unit-cauchy-filter-ℝ =
    ( equiv-unit-cauchy-filter-ℝ , is-isometry-map-unit-cauchy-filter-ℝ l)
```
