# The metric space of Cauchy filters over metric spaces

```agda
module metric-spaces.metric-space-of-cauchy-filters-metric-spaces where
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
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.expansive-maps-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
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

Let `M` be a [metric space](metric-spaces.metric-spaces.md); the type of
[Cauchy filters](metric-spaces.cauchy-filters-metric-spaces.md) inherits the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md) `N` of
`M` via the following definition: two Cauchy filters `U` and `V` are in a
`d`-neighborhood if and only if,

```text
  ∀ (α β : ℚ⁺) (x y : M) → U α x → V β y → N (α + β + d) x y
```

This neighborhood relation is an
[extensional](metric-spaces.extensionality-pseudometric-spaces.md)
[pseudometric structure](metric-spaces.pseudometric-spaces.md) on the type of
Cauchy filters defining the
{{#concept "metric space of Cauchy filters" Disambiguation="on a metric space" Agda=metric-space-Cauchy-Filter-Metric-Space}}
on `M`.

## Definitions

### Neighborhood relation on Cauchy filters

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  where

  neighborhood-prop-Cauchy-Filter-Metric-Space :
    Rational-Neighborhood-Relation
      (l1 ⊔ l2 ⊔ l)
      ( Cauchy-Filter-Metric-Space l M)
  neighborhood-prop-Cauchy-Filter-Metric-Space d U V =
    Π-Prop
      ( ℚ⁺ × ℚ⁺ × type-Metric-Space M × type-Metric-Space M)
      ( λ (α , β , x , y) →
        ℚ⁺-subset-Cauchy-Filter-Metric-Space M U α x ⇒
        ℚ⁺-subset-Cauchy-Filter-Metric-Space M V β y ⇒
        neighborhood-prop-Metric-Space M (α +ℚ⁺ β +ℚ⁺ d) x y)

  neighborhood-Cauchy-Filter-Metric-Space :
    ℚ⁺ →
    Cauchy-Filter-Metric-Space l M →
    Cauchy-Filter-Metric-Space l M →
    UU (l1 ⊔ l2 ⊔ l)
  neighborhood-Cauchy-Filter-Metric-Space d U V =
    type-Prop (neighborhood-prop-Cauchy-Filter-Metric-Space d U V)
```

### Pseudometric space of Cauchy filters

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  is-reflexive-neighborhood-Cauchy-Filter-Metric-Space :
    (d : ℚ⁺) →
    (U : Cauchy-Filter-Metric-Space l M) →
    neighborhood-Cauchy-Filter-Metric-Space M d U U
  is-reflexive-neighborhood-Cauchy-Filter-Metric-Space
    d U (α , β , x , y) Rx Ry =
    monotonic-neighborhood-Metric-Space
      ( M)
      ( x)
      ( y)
      ( α +ℚ⁺ β)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( le-left-add-ℚ⁺ (α +ℚ⁺ β) d)
      ( neighborhood-is-in-filter-Cauchy-Filter-Metric-Space M U α β x y Rx Ry)

  is-symmetric-neighborhood-Cauchy-Filter-Metric-Space :
    (d : ℚ⁺) →
    (U V : Cauchy-Filter-Metric-Space l M) →
    neighborhood-Cauchy-Filter-Metric-Space M d U V →
    neighborhood-Cauchy-Filter-Metric-Space M d V U
  is-symmetric-neighborhood-Cauchy-Filter-Metric-Space
    d U V Nuv (α , β , x , y) Rx Ry =
    tr
      ( is-upper-bound-dist-Metric-Space M x y)
      ( ap ( _+ℚ⁺ d) (commutative-add-ℚ⁺ β α))
      ( symmetric-neighborhood-Metric-Space M
        ( β +ℚ⁺ α +ℚ⁺ d)
        ( y)
        ( x)
        ( Nuv (β , α , y , x) Ry Rx))

  is-triangular-neighborhood-Cauchy-Filter-Metric-Space :
    ( U V W : Cauchy-Filter-Metric-Space l M) →
    ( ε δ : ℚ⁺) →
    neighborhood-Cauchy-Filter-Metric-Space M δ V W →
    neighborhood-Cauchy-Filter-Metric-Space M ε U V →
    neighborhood-Cauchy-Filter-Metric-Space M (ε +ℚ⁺ δ) U W
  is-triangular-neighborhood-Cauchy-Filter-Metric-Space
    U V W ε δ Nvw Nuv (α , β , x , z) Rx Rz =
    saturated-neighborhood-Metric-Space
      ( M)
      ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
      ( x)
      ( z)
      ( lemma-saturate-neighborhood)
    where

    lemma-saturate-neighborhood :
      (d : ℚ⁺) →
      neighborhood-Metric-Space M
        ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
        ( x)
        ( z)
    lemma-saturate-neighborhood d =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Metric-Space M
              ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
              ( x)
              ( z))
        in do
          (d/2 , H) ← double-le-ℚ⁺ d
          (y , Vy) ← is-total-Cauchy-Filter-Metric-Space M V d/2

          let
            lemma-interchange :
              ( ( α +ℚ⁺ d/2 +ℚ⁺ ε) +ℚ⁺ (d/2 +ℚ⁺ β +ℚ⁺ δ)) ＝
              ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ (d/2 +ℚ⁺ d/2))
            lemma-interchange =
              equational-reasoning
                ( ( α +ℚ⁺ d/2 +ℚ⁺ ε) +ℚ⁺ (d/2 +ℚ⁺ β +ℚ⁺ δ))
                ＝ ( ( α +ℚ⁺ ε +ℚ⁺ d/2) +ℚ⁺ (β +ℚ⁺ δ +ℚ⁺ d/2))
                  by
                    ap-add-ℚ⁺
                      ( ( associative-add-ℚ⁺ α d/2 ε) ∙
                        ( ap (add-ℚ⁺ α) (commutative-add-ℚ⁺ d/2 ε) ∙
                        ( inv (associative-add-ℚ⁺ α ε d/2))))
                      ( ( associative-add-ℚ⁺ d/2 β δ) ∙
                        ( commutative-add-ℚ⁺
                          ( d/2)
                          ( β +ℚ⁺ δ)))
                ＝ ( ( α +ℚ⁺ ε) +ℚ⁺ (β +ℚ⁺ δ) +ℚ⁺ (d/2 +ℚ⁺ d/2))
                  by
                    interchange-law-add-add-ℚ⁺
                      ( α +ℚ⁺ ε)
                      ( d/2)
                      ( β +ℚ⁺ δ)
                      ( d/2)
                ＝ ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ (d/2 +ℚ⁺ d/2))
                  by
                    ap
                      ( λ z → z +ℚ⁺ (d/2 +ℚ⁺ d/2))
                      ( interchange-law-add-add-ℚ⁺ α ε β δ)

          monotonic-neighborhood-Metric-Space M x z
            ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ (d/2 +ℚ⁺ d/2))
            ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
            ( preserves-le-right-add-ℚ⁺
              ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
              ( d/2 +ℚ⁺ d/2)
              ( d)
              ( H))
            ( tr
              ( is-upper-bound-dist-Metric-Space M x z)
              ( lemma-interchange)
              ( triangular-neighborhood-Metric-Space M
                ( x)
                ( y)
                ( z)
                ( α +ℚ⁺ d/2 +ℚ⁺ ε)
                ( d/2 +ℚ⁺ β +ℚ⁺ δ)
                ( Nvw (d/2 , β , y , z) Vy Rz)
                ( Nuv (α , d/2 , x , y) Rx Vy)))

  is-saturated-neighborhood-Cauchy-Filter-Metric-Space :
    ( ε : ℚ⁺) (U V : Cauchy-Filter-Metric-Space l M) →
    ( (δ : ℚ⁺) → neighborhood-Cauchy-Filter-Metric-Space M (ε +ℚ⁺ δ) U V) →
    neighborhood-Cauchy-Filter-Metric-Space M ε U V
  is-saturated-neighborhood-Cauchy-Filter-Metric-Space
    ε U V sat-N (α , β , x , y) Ux Vy =
    saturated-neighborhood-Metric-Space M
      ( α +ℚ⁺ β +ℚ⁺ ε)
      ( x)
      ( y)
      ( λ δ →
        inv-tr
          ( is-upper-bound-dist-Metric-Space M x y)
          ( associative-add-ℚ⁺ (α +ℚ⁺ β) ε δ)
          ( sat-N δ (α , β , x , y) Ux Vy))

  pseudometric-structure-Cauchy-Filter-Metric-Space :
    Pseudometric-Structure
      ( l1 ⊔ l2 ⊔ l)
      ( Cauchy-Filter-Metric-Space l M)
  pr1 pseudometric-structure-Cauchy-Filter-Metric-Space =
    neighborhood-prop-Cauchy-Filter-Metric-Space M
  pr2 pseudometric-structure-Cauchy-Filter-Metric-Space =
    ( is-reflexive-neighborhood-Cauchy-Filter-Metric-Space ,
      is-symmetric-neighborhood-Cauchy-Filter-Metric-Space ,
      is-triangular-neighborhood-Cauchy-Filter-Metric-Space ,
      is-saturated-neighborhood-Cauchy-Filter-Metric-Space)

  pseudometric-space-Cauchy-Filter-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  pseudometric-space-Cauchy-Filter-Metric-Space =
    ( Cauchy-Filter-Metric-Space l M ,
      pseudometric-structure-Cauchy-Filter-Metric-Space)
```

### Extensionality of the pseudometric structure

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  where

  neighborhood-is-in-filter-sim-Cauchy-Filter-Metric-Space :
    (U V : Cauchy-Filter-Metric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( U)
      ( V) →
    ( α β : ℚ⁺) →
    ( x y : type-Metric-Space M) →
    is-in-filter-Cauchy-Filter-Metric-Space M U α x →
    is-in-filter-Cauchy-Filter-Metric-Space M V β y →
    neighborhood-Metric-Space M (α +ℚ⁺ β) x y
  neighborhood-is-in-filter-sim-Cauchy-Filter-Metric-Space
    U V U~V α β x y Ux Vy =
    saturated-neighborhood-Metric-Space M
      ( α +ℚ⁺ β)
      ( x)
      ( y)
      ( λ d → U~V d (α , β , x , y) Ux Vy)

  is-in-filter-add-sim-Cauchy-Filter-Metric-Space :
    (U V : Cauchy-Filter-Metric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( U)
      ( V) →
    ( α β : ℚ⁺) →
    ( x : type-Metric-Space M) →
    is-in-filter-Cauchy-Filter-Metric-Space M U α x →
    is-in-filter-Cauchy-Filter-Metric-Space M V (α +ℚ⁺ β) x
  is-in-filter-add-sim-Cauchy-Filter-Metric-Space U V U~V α β x Ux =
    let
      open
        do-syntax-trunc-Prop
          ( ℚ⁺-subset-Cauchy-Filter-Metric-Space M V (α +ℚ⁺ β) x)
      in do
        (β/2 , H) ← double-le-ℚ⁺ β
        (y , Vy) ← is-total-Cauchy-Filter-Metric-Space M V β/2

        let
          Nxy : neighborhood-Metric-Space M (α +ℚ⁺ β/2) x y
          Nxy =
            neighborhood-is-in-filter-sim-Cauchy-Filter-Metric-Space
              ( U)
              ( V)
              ( U~V)
              ( α)
              ( β/2)
              ( x)
              ( y)
              ( Ux)
              ( Vy)

          Vx :
            is-in-filter-Cauchy-Filter-Metric-Space
              ( M)
              ( V)
              ( β/2 +ℚ⁺ (α +ℚ⁺ β/2))
              ( x)
          Vx =
            is-in-filter-neighborhood-Cauchy-Filter-Metric-Space
              ( M)
              ( V)
              ( β/2)
              ( α +ℚ⁺ β/2)
              ( y)
              ( x)
              ( Vy)
              ( symmetric-neighborhood-Metric-Space M _ x y Nxy)

          lemma-le-αβ : le-ℚ⁺ (β/2 +ℚ⁺ (α +ℚ⁺ β/2)) (α +ℚ⁺ β)
          lemma-le-αβ =
            inv-tr
              ( λ d → le-ℚ⁺ d (α +ℚ⁺ β))
              ( commutative-add-ℚ⁺ β/2 (α +ℚ⁺ β/2) ∙
                associative-add-ℚ⁺ α β/2 β/2)
              ( preserves-le-right-add-ℚ⁺ α (β/2 +ℚ⁺ β/2) β H)

        is-monotonic-filter-Cauchy-Filter-Metric-Space
          ( M)
          ( V)
          ( x)
          ( β/2 +ℚ⁺ (α +ℚ⁺ β/2))
          ( α +ℚ⁺ β)
          ( lemma-le-αβ)
          ( Vx)

  htpy-filter-sim-Cauchy-Filter-Metric-Space :
    (U V : Cauchy-Filter-Metric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( U)
      ( V) →
    ( α : ℚ⁺) →
    ℚ⁺-subset-Cauchy-Filter-Metric-Space M U α ~
    ℚ⁺-subset-Cauchy-Filter-Metric-Space M V α
  htpy-filter-sim-Cauchy-Filter-Metric-Space U V U~V α x =
    eq-iff
      ( λ Ux →
        is-saturated-Cauchy-Filter-Metric-Space
          ( M)
          ( V)
          ( α)
          ( x)
          ( λ δ →
            is-in-filter-add-sim-Cauchy-Filter-Metric-Space U V U~V α δ x Ux))
      ( λ Vx →
        is-saturated-Cauchy-Filter-Metric-Space
          ( M)
          ( U)
          ( α)
          ( x)
          ( λ δ →
            is-in-filter-add-sim-Cauchy-Filter-Metric-Space
              ( V)
              ( U)
              ( symmetric-sim-Pseudometric-Space
              ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
                ( U)
                ( V)
                ( U~V))
              ( α)
              ( δ)
              ( x)
              ( Vx)))

  eq-filter-sim-Cauchy-Filter-Metric-Space :
    (U V : Cauchy-Filter-Metric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( U)
      ( V) →
    ℚ⁺-subset-Cauchy-Filter-Metric-Space M U ＝
    ℚ⁺-subset-Cauchy-Filter-Metric-Space M V
  eq-filter-sim-Cauchy-Filter-Metric-Space U V U~V =
    eq-htpy
      ( λ α →
        eq-htpy
          ( htpy-filter-sim-Cauchy-Filter-Metric-Space U V U~V α))

  eq-sim-Cauchy-Filter-Metric-Space :
    (U V : Cauchy-Filter-Metric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( U)
      ( V) →
    U ＝ V
  eq-sim-Cauchy-Filter-Metric-Space U V U~V =
    eq-type-subtype
      ( is-cauchy-prop-ℚ⁺-subset-Metric-Space l M)
      ( eq-filter-sim-Cauchy-Filter-Metric-Space U V U~V)

  is-extensional-pseudometric-space-Cauchy-Filter-Metric-Space :
    is-extensional-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
  is-extensional-pseudometric-space-Cauchy-Filter-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-space-Cauchy-Filter-Metric-Space l M)
      ( eq-sim-Cauchy-Filter-Metric-Space)
```

### The metric space of Cauchy filters on a metric space

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  metric-space-Cauchy-Filter-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  metric-space-Cauchy-Filter-Metric-Space =
    ( pseudometric-space-Cauchy-Filter-Metric-Space l M ,
      is-extensional-pseudometric-space-Cauchy-Filter-Metric-Space M)
```

## Properties

### The unit map is an isometry

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-short-map-unit-Cauchy-Filter-Metric-Space :
    is-short-map-Metric-Space
      ( M)
      ( metric-space-Cauchy-Filter-Metric-Space l2 M)
      ( map-unit-Cauchy-Filter-Metric-Space M)
  is-short-map-unit-Cauchy-Filter-Metric-Space
    d y z Nyz (α , β , u , v) Nyu Nzv =
    inv-tr
      ( is-upper-bound-dist-Metric-Space M u v)
      ( associative-add-ℚ⁺ α β d ∙
        ap (add-ℚ⁺ α) (commutative-add-ℚ⁺ β d) ∙
        inv (associative-add-ℚ⁺ α d β))
      ( Nuv)
    where

    Nuv : neighborhood-Metric-Space M (α +ℚ⁺ d +ℚ⁺ β) u v
    Nuv =
      triangular-neighborhood-Metric-Space M
        ( u)
        ( z)
        ( v)
        ( α +ℚ⁺ d)
        ( β)
        ( Nzv)
        ( triangular-neighborhood-Metric-Space M
          ( u)
          ( y)
          ( z)
          ( α)
          ( d)
          ( Nyz)
          ( symmetric-neighborhood-Metric-Space M α y u Nyu))

  is-expansive-map-unit-Cauchy-Filter-Metric-Space :
    is-expansive-map-Metric-Space
      ( M)
      ( metric-space-Cauchy-Filter-Metric-Space l2 M)
      ( map-unit-Cauchy-Filter-Metric-Space M)
  is-expansive-map-unit-Cauchy-Filter-Metric-Space
    d y z Nyz =
    saturated-neighborhood-Metric-Space M d y z lemma-saturate-neighborhood
    where

    lemma-bisaturate-neighborhood :
      (α β : ℚ⁺) →
      neighborhood-Metric-Space M (α +ℚ⁺ β +ℚ⁺ d) y z
    lemma-bisaturate-neighborhood α β =
      Nyz
        (α , β , y , z)
        ( refl-neighborhood-Metric-Space M α y)
        ( refl-neighborhood-Metric-Space M β z)

    lemma-saturate-neighborhood :
      (δ : ℚ⁺) → neighborhood-Metric-Space M (d +ℚ⁺ δ) y z
    lemma-saturate-neighborhood δ =
      tr
        ( is-upper-bound-dist-Metric-Space M y z)
        ( ap (_+ℚ⁺ d) (eq-add-split-ℚ⁺ δ) ∙ commutative-add-ℚ⁺ δ d)
        ( lemma-bisaturate-neighborhood
          ( left-summand-split-ℚ⁺ δ)
          ( right-summand-split-ℚ⁺ δ))

  is-isometry-map-unit-Cauchy-Filter-Metric-Space :
    is-isometry-Metric-Space
      ( M)
      ( metric-space-Cauchy-Filter-Metric-Space l2 M)
      ( map-unit-Cauchy-Filter-Metric-Space M)
  is-isometry-map-unit-Cauchy-Filter-Metric-Space =
    is-isometry-is-expansive-map-is-short-map-Metric-Space
      ( M)
      ( metric-space-Cauchy-Filter-Metric-Space l2 M)
      ( map-unit-Cauchy-Filter-Metric-Space M)
      ( is-short-map-unit-Cauchy-Filter-Metric-Space)
      ( is-expansive-map-unit-Cauchy-Filter-Metric-Space)

  isometry-unit-Cauchy-Filter-Metric-Space :
    isometry-Metric-Space M (metric-space-Cauchy-Filter-Metric-Space l2 M)
  isometry-unit-Cauchy-Filter-Metric-Space =
    ( map-unit-Cauchy-Filter-Metric-Space M ,
      is-isometry-map-unit-Cauchy-Filter-Metric-Space)
```
