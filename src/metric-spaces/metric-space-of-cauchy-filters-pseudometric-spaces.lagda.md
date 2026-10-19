# The metric space of Cauchy filters in a pseudometric space

```agda
module metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces where
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
open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.expansive-maps-metric-spaces
open import metric-spaces.expansive-maps-pseudometric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
```

</details>

## Idea

The type of
[Cauchy filters](metric-spaces.cauchy-filters-pseudometric-spaces.md) on a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `M` inherits the
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
{{#concept "metric space of Cauchy filters" Disambiguation="on a pseudometric space" Agda=metric-space-cauchy-filter-Pseudometric-Space}}
on `M`.

## Definitions

### Neighborhood relation on Cauchy filters

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  where

  neighborhood-prop-cauchy-filter-Pseudometric-Space :
    Rational-Neighborhood-Relation
      (l1 ⊔ l2 ⊔ l)
      ( cauchy-filter-Pseudometric-Space l M)
  neighborhood-prop-cauchy-filter-Pseudometric-Space d U V =
    Π-Prop
      ( ℚ⁺ × ℚ⁺ × type-Pseudometric-Space M × type-Pseudometric-Space M)
      ( λ (α , β , x , y) →
        neighborhood-subtype-cauchy-filter-Pseudometric-Space M U α x ⇒
        neighborhood-subtype-cauchy-filter-Pseudometric-Space M V β y ⇒
        neighborhood-prop-Pseudometric-Space M (α +ℚ⁺ β +ℚ⁺ d) x y)

  neighborhood-cauchy-filter-Pseudometric-Space :
    ℚ⁺ →
    cauchy-filter-Pseudometric-Space l M →
    cauchy-filter-Pseudometric-Space l M →
    UU (l1 ⊔ l2 ⊔ l)
  neighborhood-cauchy-filter-Pseudometric-Space d U V =
    type-Prop (neighborhood-prop-cauchy-filter-Pseudometric-Space d U V)
```

### Pseudometric space of Cauchy filters

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where abstract

  is-reflexive-neighborhood-cauchy-filter-Pseudometric-Space :
    (d : ℚ⁺) →
    (U : cauchy-filter-Pseudometric-Space l M) →
    neighborhood-cauchy-filter-Pseudometric-Space M d U U
  is-reflexive-neighborhood-cauchy-filter-Pseudometric-Space
    d U (α , β , x , y) Rx Ry =
    monotonic-neighborhood-Pseudometric-Space
      ( M)
      ( x)
      ( y)
      ( α +ℚ⁺ β)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( le-left-add-ℚ⁺ (α +ℚ⁺ β) d)
      ( is-bounded-cauchy-filter-Pseudometric-Space M U α β x y Rx Ry)

  is-symmetric-neighborhood-cauchy-filter-Pseudometric-Space :
    (d : ℚ⁺) →
    (U V : cauchy-filter-Pseudometric-Space l M) →
    neighborhood-cauchy-filter-Pseudometric-Space M d U V →
    neighborhood-cauchy-filter-Pseudometric-Space M d V U
  is-symmetric-neighborhood-cauchy-filter-Pseudometric-Space
    d U V Nuv (α , β , x , y) Rx Ry =
    tr
      ( is-upper-bound-dist-Pseudometric-Space M x y)
      ( ap ( _+ℚ⁺ d) (commutative-add-ℚ⁺ β α))
      ( symmetric-neighborhood-Pseudometric-Space M
        ( β +ℚ⁺ α +ℚ⁺ d)
        ( y)
        ( x)
        ( Nuv (β , α , y , x) Ry Rx))

  is-triangular-neighborhood-cauchy-filter-Pseudometric-Space :
    ( U V W : cauchy-filter-Pseudometric-Space l M) →
    ( ε δ : ℚ⁺) →
    neighborhood-cauchy-filter-Pseudometric-Space M δ V W →
    neighborhood-cauchy-filter-Pseudometric-Space M ε U V →
    neighborhood-cauchy-filter-Pseudometric-Space M (ε +ℚ⁺ δ) U W
  is-triangular-neighborhood-cauchy-filter-Pseudometric-Space
    U V W ε δ Nvw Nuv (α , β , x , z) Rx Rz =
    saturated-neighborhood-Pseudometric-Space
      ( M)
      ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
      ( x)
      ( z)
      ( lemma-saturate-neighborhood)
    where

    lemma-saturate-neighborhood :
      (d : ℚ⁺) →
      neighborhood-Pseudometric-Space M
        ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
        ( x)
        ( z)
    lemma-saturate-neighborhood d =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Pseudometric-Space M
              ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
              ( x)
              ( z))
        in do
          (d/2 , H) ← double-le-ℚ⁺ d
          (y , Vy) ← is-proper-cauchy-filter-Pseudometric-Space M V d/2

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

          monotonic-neighborhood-Pseudometric-Space M x z
            ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ (d/2 +ℚ⁺ d/2))
            ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ) +ℚ⁺ d)
            ( preserves-le-right-add-ℚ⁺
              ( α +ℚ⁺ β +ℚ⁺ (ε +ℚ⁺ δ))
              ( d/2 +ℚ⁺ d/2)
              ( d)
              ( H))
            ( tr
              ( is-upper-bound-dist-Pseudometric-Space M x z)
              ( lemma-interchange)
              ( triangular-neighborhood-Pseudometric-Space M
                ( x)
                ( y)
                ( z)
                ( α +ℚ⁺ d/2 +ℚ⁺ ε)
                ( d/2 +ℚ⁺ β +ℚ⁺ δ)
                ( Nvw (d/2 , β , y , z) Vy Rz)
                ( Nuv (α , d/2 , x , y) Rx Vy)))

  is-saturated-neighborhood-cauchy-filter-Pseudometric-Space :
    ( ε : ℚ⁺) (U V : cauchy-filter-Pseudometric-Space l M) →
    ( (δ : ℚ⁺) →
      neighborhood-cauchy-filter-Pseudometric-Space M (ε +ℚ⁺ δ) U V) →
    neighborhood-cauchy-filter-Pseudometric-Space M ε U V
  is-saturated-neighborhood-cauchy-filter-Pseudometric-Space
    ε U V sat-N (α , β , x , y) Ux Vy =
    saturated-neighborhood-Pseudometric-Space M
      ( α +ℚ⁺ β +ℚ⁺ ε)
      ( x)
      ( y)
      ( λ δ →
        inv-tr
          ( is-upper-bound-dist-Pseudometric-Space M x y)
          ( associative-add-ℚ⁺ (α +ℚ⁺ β) ε δ)
          ( sat-N δ (α , β , x , y) Ux Vy))
```

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  pseudometric-structure-cauchy-filter-Pseudometric-Space :
    Pseudometric-Structure
      ( l1 ⊔ l2 ⊔ l)
      ( cauchy-filter-Pseudometric-Space l M)
  pr1 pseudometric-structure-cauchy-filter-Pseudometric-Space =
    neighborhood-prop-cauchy-filter-Pseudometric-Space M
  pr2 pseudometric-structure-cauchy-filter-Pseudometric-Space =
    ( is-reflexive-neighborhood-cauchy-filter-Pseudometric-Space l M ,
      is-symmetric-neighborhood-cauchy-filter-Pseudometric-Space l M ,
      is-triangular-neighborhood-cauchy-filter-Pseudometric-Space l M ,
      is-saturated-neighborhood-cauchy-filter-Pseudometric-Space l M)

  pseudometric-space-cauchy-filter-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  pseudometric-space-cauchy-filter-Pseudometric-Space =
    ( cauchy-filter-Pseudometric-Space l M ,
      pseudometric-structure-cauchy-filter-Pseudometric-Space)
```

### Extensionality of the pseudometric structure

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  where abstract

  neighborhood-is-in-filter-sim-cauchy-filter-Pseudometric-Space :
    (U V : cauchy-filter-Pseudometric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( U)
      ( V) →
    ( α β : ℚ⁺) →
    ( x y : type-Pseudometric-Space M) →
    is-in-cauchy-filter-Pseudometric-Space M U α x →
    is-in-cauchy-filter-Pseudometric-Space M V β y →
    neighborhood-Pseudometric-Space M (α +ℚ⁺ β) x y
  neighborhood-is-in-filter-sim-cauchy-filter-Pseudometric-Space
    U V U~V α β x y Ux Vy =
    saturated-neighborhood-Pseudometric-Space M
      ( α +ℚ⁺ β)
      ( x)
      ( y)
      ( λ d → U~V d (α , β , x , y) Ux Vy)

  is-in-filter-add-sim-cauchy-filter-Pseudometric-Space :
    (U V : cauchy-filter-Pseudometric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( U)
      ( V) →
    ( α β : ℚ⁺) →
    ( x : type-Pseudometric-Space M) →
    is-in-cauchy-filter-Pseudometric-Space M U α x →
    is-in-cauchy-filter-Pseudometric-Space M V (α +ℚ⁺ β) x
  is-in-filter-add-sim-cauchy-filter-Pseudometric-Space U V U~V α β x Ux =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-subtype-cauchy-filter-Pseudometric-Space
            ( M)
            ( V)
            ( α +ℚ⁺ β)
            ( x))
      in do
        (β/2 , H) ← double-le-ℚ⁺ β
        (y , Vy) ← is-proper-cauchy-filter-Pseudometric-Space M V β/2

        let
          Nxy : neighborhood-Pseudometric-Space M (α +ℚ⁺ β/2) x y
          Nxy =
            neighborhood-is-in-filter-sim-cauchy-filter-Pseudometric-Space
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
            is-in-cauchy-filter-Pseudometric-Space
              ( M)
              ( V)
              ( β/2 +ℚ⁺ (α +ℚ⁺ β/2))
              ( x)
          Vx =
            is-enclosing-cauchy-filter-Pseudometric-Space
              ( M)
              ( V)
              ( β/2)
              ( α +ℚ⁺ β/2)
              ( y)
              ( x)
              ( Vy)
              ( symmetric-neighborhood-Pseudometric-Space M _ x y Nxy)

          lemma-le-αβ : le-ℚ⁺ (β/2 +ℚ⁺ (α +ℚ⁺ β/2)) (α +ℚ⁺ β)
          lemma-le-αβ =
            inv-tr
              ( λ d → le-ℚ⁺ d (α +ℚ⁺ β))
              ( commutative-add-ℚ⁺ β/2 (α +ℚ⁺ β/2) ∙
                associative-add-ℚ⁺ α β/2 β/2)
              ( preserves-le-right-add-ℚ⁺ α (β/2 +ℚ⁺ β/2) β H)

        is-monotonic-cauchy-filter-Pseudometric-Space
          ( M)
          ( V)
          ( x)
          ( β/2 +ℚ⁺ (α +ℚ⁺ β/2))
          ( α +ℚ⁺ β)
          ( lemma-le-αβ)
          ( Vx)

  htpy-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space :
    (U V : cauchy-filter-Pseudometric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( U)
      ( V) →
    ( α : ℚ⁺) →
    neighborhood-subtype-cauchy-filter-Pseudometric-Space M U α ~
    neighborhood-subtype-cauchy-filter-Pseudometric-Space M V α
  htpy-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space U V U~V α x =
    eq-iff
      ( λ Ux →
        is-saturated-cauchy-filter-Pseudometric-Space
          ( M)
          ( V)
          ( α , x)
          ( λ δ →
            is-in-filter-add-sim-cauchy-filter-Pseudometric-Space
              U
              V
              U~V
              α
              δ
              x
              Ux))
      ( λ Vx →
        is-saturated-cauchy-filter-Pseudometric-Space
          ( M)
          ( U)
          ( α , x)
          ( λ δ →
            is-in-filter-add-sim-cauchy-filter-Pseudometric-Space
              ( V)
              ( U)
              ( symmetric-sim-Pseudometric-Space
                ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
                  ( U)
                  ( V)
                  ( U~V))
              ( α)
              ( δ)
              ( x)
              ( Vx)))

  eq-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space :
    (U V : cauchy-filter-Pseudometric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( U)
      ( V) →
    neighborhood-subtype-cauchy-filter-Pseudometric-Space M U ＝
    neighborhood-subtype-cauchy-filter-Pseudometric-Space M V
  eq-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space U V U~V =
    eq-htpy
      ( λ α →
        eq-htpy
          ( htpy-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space
            ( U)
            ( V)
            ( U~V)
            ( α)))

  eq-sim-cauchy-filter-Pseudometric-Space :
    (U V : cauchy-filter-Pseudometric-Space l M) →
    sim-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( U)
      ( V) →
    U ＝ V
  eq-sim-cauchy-filter-Pseudometric-Space U V U~V =
    eq-type-subtype
      ( is-cauchy-filter-prop-Pseudometric-Space l M)
      ( eq-neighborhood-subtype-sim-cauchy-filter-Pseudometric-Space U V U~V)

  is-extensional-pseudometric-space-cauchy-filter-Pseudometric-Space :
    is-extensional-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
  is-extensional-pseudometric-space-cauchy-filter-Pseudometric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l M)
      ( eq-sim-cauchy-filter-Pseudometric-Space)
```

### The metric space of Cauchy filters on a pseudometric space

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  metric-space-cauchy-filter-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  metric-space-cauchy-filter-Pseudometric-Space =
    ( pseudometric-space-cauchy-filter-Pseudometric-Space l M ,
      is-extensional-pseudometric-space-cauchy-filter-Pseudometric-Space M)
```

## Properties

### The unit map is an isometry

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-short-map-unit-cauchy-filter-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( M)
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l2 M)
      ( map-unit-cauchy-filter-Pseudometric-Space M)
  is-short-map-unit-cauchy-filter-Pseudometric-Space
    d y z Nyz (α , β , u , v) Nyu Nzv =
    inv-tr
      ( is-upper-bound-dist-Pseudometric-Space M u v)
      ( associative-add-ℚ⁺ α β d ∙
        ap (add-ℚ⁺ α) (commutative-add-ℚ⁺ β d) ∙
        inv (associative-add-ℚ⁺ α d β))
      ( Nuv)
    where

    Nuv : neighborhood-Pseudometric-Space M (α +ℚ⁺ d +ℚ⁺ β) u v
    Nuv =
      triangular-neighborhood-Pseudometric-Space M
        ( u)
        ( z)
        ( v)
        ( α +ℚ⁺ d)
        ( β)
        ( Nzv)
        ( triangular-neighborhood-Pseudometric-Space M
          ( u)
          ( y)
          ( z)
          ( α)
          ( d)
          ( Nyz)
          ( symmetric-neighborhood-Pseudometric-Space M α y u Nyu))

  is-expansive-map-unit-cauchy-filter-Pseudometric-Space :
    is-expansive-map-Pseudometric-Space
      ( M)
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l2 M)
      ( map-unit-cauchy-filter-Pseudometric-Space M)
  is-expansive-map-unit-cauchy-filter-Pseudometric-Space
    d y z Nyz =
    saturated-neighborhood-Pseudometric-Space
      ( M)
      ( d)
      ( y)
      ( z)
      (lemma-saturate-neighborhood)
    where

    lemma-bisaturate-neighborhood :
      (α β : ℚ⁺) →
      neighborhood-Pseudometric-Space M (α +ℚ⁺ β +ℚ⁺ d) y z
    lemma-bisaturate-neighborhood α β =
      Nyz
        (α , β , y , z)
        ( refl-neighborhood-Pseudometric-Space M α y)
        ( refl-neighborhood-Pseudometric-Space M β z)

    lemma-saturate-neighborhood :
      (δ : ℚ⁺) → neighborhood-Pseudometric-Space M (d +ℚ⁺ δ) y z
    lemma-saturate-neighborhood δ =
      tr
        ( is-upper-bound-dist-Pseudometric-Space M y z)
        ( ap (_+ℚ⁺ d) (eq-add-split-ℚ⁺ δ) ∙ commutative-add-ℚ⁺ δ d)
        ( lemma-bisaturate-neighborhood
          ( left-summand-split-ℚ⁺ δ)
          ( right-summand-split-ℚ⁺ δ))

  is-isometry-map-unit-cauchy-filter-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l2 M)
      ( map-unit-cauchy-filter-Pseudometric-Space M)
  is-isometry-map-unit-cauchy-filter-Pseudometric-Space =
    is-isometry-is-expansive-map-is-short-map-Pseudometric-Space
      ( M)
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l2 M)
      ( map-unit-cauchy-filter-Pseudometric-Space M)
      ( is-short-map-unit-cauchy-filter-Pseudometric-Space)
      ( is-expansive-map-unit-cauchy-filter-Pseudometric-Space)

  isometry-unit-cauchy-filter-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( M)
      ( pseudometric-space-cauchy-filter-Pseudometric-Space l2 M)
  isometry-unit-cauchy-filter-Pseudometric-Space =
    ( map-unit-cauchy-filter-Pseudometric-Space M ,
      is-isometry-map-unit-cauchy-filter-Pseudometric-Space)
```
