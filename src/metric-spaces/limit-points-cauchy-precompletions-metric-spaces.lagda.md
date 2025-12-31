# Cauchy precompletions limit points of extensions of metric spaces

```agda
module metric-spaces.limit-points-cauchy-precompletions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-dense-extensions-metric-spaces
open import metric-spaces.cauchy-precompletions-metric-spaces
open import metric-spaces.cauchy-precompletions-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limit-points-extensions-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Given an [extension](metric-spaces.extensions-metric-spaces.md) of
[metric spaces](metric-spaces.metric-spaces.md) `i : M → U`, a point `y : U` is
a [limit point](metric-spaces.limit-points-extensions-metric-spaces.md) of the
extension if and only if there exists a unique `X : [C M]` in the
[Cauchy precompletion](metric-spaces.cauchy-precompletions-metric-spaces.md) of
`M` such that all
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
the [class](metric-spaces.metric-quotients-of-pseudometric-spaces.md) of `X`.

## Definitions

### Limits in extemnsions of metric spaces of elements of the Cauchy precompletion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (y : type-metric-space-extension-Metric-Space M U)
  (X : type-cauchy-precompletion-Metric-Space M)
  where

  is-limit-prop-cauchy-precompletion-extension-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l4)
  is-limit-prop-cauchy-precompletion-extension-Metric-Space =
    Π-Prop
      ( type-subtype-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( X))
      ( λ (x , x∈X) →
        is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space
          ( M)
          ( U)
          ( y)
          ( x))

  is-limit-cauchy-precompletion-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-limit-cauchy-precompletion-extension-Metric-Space =
    type-Prop
      is-limit-prop-cauchy-precompletion-extension-Metric-Space

  is-prop-is-limit-cauchy-precompletion-extension-Metric-Space :
    is-prop
      ( is-limit-cauchy-precompletion-extension-Metric-Space)
  is-prop-is-limit-cauchy-precompletion-extension-Metric-Space =
    is-prop-type-Prop
      is-limit-prop-cauchy-precompletion-extension-Metric-Space
```

### The property of being the limit of an element in the Cauchy precompletion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (u : type-metric-space-extension-Metric-Space M U)
  where

  is-limit-cauchy-precompletion-point-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-limit-cauchy-precompletion-point-extension-Metric-Space =
    Σ ( type-cauchy-precompletion-Metric-Space M)
      ( is-limit-cauchy-precompletion-extension-Metric-Space M U u)

  lemma-all-eq-limit-cauchy-precompletion-point-extension-Metric-Space :
    (X Y : type-cauchy-precompletion-Metric-Space M) →
    is-limit-cauchy-precompletion-extension-Metric-Space M U u X →
    is-limit-cauchy-precompletion-extension-Metric-Space M U u Y →
    X ＝ Y
  lemma-all-eq-limit-cauchy-precompletion-point-extension-Metric-Space
    X Y lim-X lim-Y =
    let
      open
        do-syntax-trunc-Prop
          ( eq-prop-Metric-Space
            ( cauchy-precompletion-Metric-Space M)
            ( X)
            ( Y))
      in do
        ( x , x∈X) ←
          is-inhabited-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( X)

        ( y , y∈Y) ←
          is-inhabited-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( Y)

        let
          x~y :
            sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space M)
              ( x)
              ( y)
          x~y =
            sim-has-same-limit-map-cauchy-pseudocompletion-extension-Metric-Space
              ( M)
              ( U)
              ( u)
              ( x)
              ( y)
              ( lim-X (x , x∈X))
              ( lim-Y (y , y∈Y))

        eq-set-quotient-sim-element-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M))
          ( X)
          ( Y)
          ( x∈X)
          ( y∈Y)
          ( x~y)

  all-eq-is-limit-cauchy-precompletion-point-extension-Metric-Space :
    (X Y : is-limit-cauchy-precompletion-point-extension-Metric-Space) →
    X ＝ Y
  all-eq-is-limit-cauchy-precompletion-point-extension-Metric-Space X Y =
    eq-type-subtype
      ( is-limit-prop-cauchy-precompletion-extension-Metric-Space M U u)
      ( lemma-all-eq-limit-cauchy-precompletion-point-extension-Metric-Space
        ( pr1 X)
        ( pr1 Y)
        ( pr2 X)
        ( pr2 Y))

  is-prop-is-limit-cauchy-precompletion-point-extension-Metric-Space :
    is-prop
      ( is-limit-cauchy-precompletion-point-extension-Metric-Space)
  is-prop-is-limit-cauchy-precompletion-point-extension-Metric-Space =
    is-prop-all-elements-equal
      all-eq-is-limit-cauchy-precompletion-point-extension-Metric-Space

  is-limit-cauchy-precompletion-prop-point-extension-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l4)
  is-limit-cauchy-precompletion-prop-point-extension-Metric-Space =
    ( is-limit-cauchy-precompletion-point-extension-Metric-Space ,
      is-prop-is-limit-cauchy-precompletion-point-extension-Metric-Space)
```

## Properties

### Limit points are limit points of elements of the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (u : type-metric-space-extension-Metric-Space M U)
  (x : cauchy-approximation-Metric-Space M)
  where

  is-limit-map-quotient-cauchy-pseudocompletion-extension-Metric-Space :
    is-limit-map-cauchy-pseudocompletion-extension-Metric-Space
      ( M)
      ( U)
      ( u)
      ( x) →
    is-limit-cauchy-precompletion-extension-Metric-Space
      ( M)
      ( U)
      ( u)
      ( map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space
        ( M)
        ( x))
  is-limit-map-quotient-cauchy-pseudocompletion-extension-Metric-Space
    lim-x (y , y∈[x]) =
    has-same-limit-map-cauchy-sim-pseudocompletion-extension-Metric-Space
      ( M)
      ( U)
      ( u)
      ( x)
      ( y)
      ( sim-is-in-equivalence-class-quotient-map-set-quotient
        ( equivalence-relation-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M))
        ( x)
        ( y)
        ( y∈[x]))
      ( lim-x)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (u : type-metric-space-extension-Metric-Space M U)
  where

  is-limit-cauchy-precompletion-is-limit-point-extension-Metric-Space :
    is-limit-point-extension-Metric-Space M U u →
    is-limit-cauchy-precompletion-point-extension-Metric-Space M U u
  is-limit-cauchy-precompletion-is-limit-point-extension-Metric-Space =
    elim-exists
      ( is-limit-cauchy-precompletion-prop-point-extension-Metric-Space M U u)
      ( λ x lim-x →
        ( ( map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space
            ( M)
            ( x)) ,
          ( is-limit-map-quotient-cauchy-pseudocompletion-extension-Metric-Space
            ( M)
            ( U)
            ( u)
            ( x)
            ( lim-x))))

  is-limit-point-extension-is-limit-cauchy-precompletion-extension-Metric-Space :
    is-limit-cauchy-precompletion-point-extension-Metric-Space M U u →
    is-limit-point-extension-Metric-Space M U u
  is-limit-point-extension-is-limit-cauchy-precompletion-extension-Metric-Space
    (X , lim-X) =
    elim-exists
      ( is-limit-prop-point-extension-Metric-Space M U u)
      ( λ x x∈X → intro-exists x (lim-X (x , x∈X)))
      ( is-inhabited-class-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( X))
```

### Cauchy dense extensions extend into the Cauchy precompletion

#### The map from Cauchy-dense extensions into the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (dense-U : is-cauchy-dense-extension-Metric-Space M U)
  (u : type-metric-space-extension-Metric-Space M U)
  where

  is-limit-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space :
    is-limit-cauchy-precompletion-point-extension-Metric-Space
      ( M)
      ( U)
      ( u)
  is-limit-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space =
    is-limit-cauchy-precompletion-is-limit-point-extension-Metric-Space
      ( M)
      ( U)
      ( u)
      ( dense-U u)

  map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    type-cauchy-precompletion-Metric-Space M
  map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space =
    pr1
      is-limit-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space

  is-limit-map-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space :
    is-limit-cauchy-precompletion-extension-Metric-Space
      ( M)
      ( U)
      ( u)
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space)
  is-limit-map-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space
    =
    pr2
      is-limit-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space

  sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    (x : cauchy-approximation-Metric-Space M) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space)
      ( x) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M U))
      ( map-cauchy-approximation-extension-Metric-Space M U x)
      ( map-cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M U)
        ( u))
  sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space x x∈X =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( map-cauchy-approximation-extension-Metric-Space M U x)
      ( u)
      ( is-limit-map-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space
        ( x , x∈X))
```

#### The map from Cauchy-dense extensions into the Cauchy precompletion is an isometry

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (dense-U : is-cauchy-dense-extension-Metric-Space M U)
  where abstract

  preserves-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    (d : ℚ⁺) →
    (u v : type-metric-space-extension-Metric-Space M U) →
    neighborhood-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( d)
      ( u)
      ( v) →
    neighborhood-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( d)
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( M)
        ( U)
        ( dense-U)
        ( u))
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( M)
        ( U)
        ( dense-U)
        ( v))
  preserves-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
    d u v Nuv (x , x∈[u]) (y , y∈[v]) =
    let
      ιx~κu :
        sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( map-cauchy-approximation-extension-Metric-Space M U x)
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( u))
      ιx~κu =
        sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
          ( M)
          ( U)
          ( dense-U)
          ( u)
          ( x)
          ( x∈[u])

      ιy~κv :
        sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( map-cauchy-approximation-extension-Metric-Space M U y)
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( v))
      ιy~κv =
        sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
          ( M)
          ( U)
          ( dense-U)
          ( v)
          ( y)
          ( y∈[v])

      N[κu][κv] :
        neighborhood-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( d)
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( u))
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( v))
      N[κu][κv] =
        preserves-neighborhoods-map-isometry-Pseudometric-Space
          ( pseudometric-space-extension-Metric-Space M U)
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( isometry-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( d)
          ( u)
          ( v)
          ( Nuv)

      N[ιx][ιy] :
        neighborhood-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          ( d)
          ( map-cauchy-approximation-extension-Metric-Space M U x)
          ( map-cauchy-approximation-extension-Metric-Space M U y)
      N[ιx][ιy] =
        reflects-neighborhoods-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          { map-cauchy-approximation-extension-Metric-Space M U x}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( u)}
          { map-cauchy-approximation-extension-Metric-Space M U y}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( v)}
          ( ιx~κu)
          ( ιy~κv)
          ( d)
          ( N[κu][κv])

    in
      reflects-neighborhoods-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M U))
        ( isometry-cauchy-pseudocompletion-extension-Metric-Space M U)
        ( d)
        ( x)
        ( y)
        ( N[ιx][ιy])

  reflects-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    (d : ℚ⁺) →
    (u v : type-metric-space-extension-Metric-Space M U) →
    neighborhood-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( d)
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( M)
        ( U)
        ( dense-U)
        ( u))
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( M)
        ( U)
        ( dense-U)
        ( v)) →
    neighborhood-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( d)
      ( u)
      ( v)
  reflects-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
    d u v N[u][v] =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( d)
            ( u)
            ( v))
    in do
      (x , x∈[u]) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M)
          ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
            ( M)
            ( U)
            ( dense-U)
            ( u))

      (y , y∈[v]) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M)
          ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
            ( M)
            ( U)
            ( dense-U)
            ( v))

      let
        ιx~κu :
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M U))
            ( map-cauchy-approximation-extension-Metric-Space M U x)
            ( map-cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M U)
              ( u))
        ιx~κu =
          sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
            ( M)
            ( U)
            ( dense-U)
            ( u)
            ( x)
            ( x∈[u])

        ιy~κv :
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M U))
            ( map-cauchy-approximation-extension-Metric-Space M U y)
            ( map-cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M U)
              ( v))
        ιy~κv =
          sim-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
            ( M)
            ( U)
            ( dense-U)
            ( v)
            ( y)
            ( y∈[v])

      reflects-neighborhoods-map-isometry-Pseudometric-Space
        ( pseudometric-space-extension-Metric-Space M U)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M U))
        ( isometry-cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M U))
        ( d)
        ( u)
        ( v)
        ( preserves-neighborhoods-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U))
          { map-cauchy-approximation-extension-Metric-Space M U x}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( u)}
          { map-cauchy-approximation-extension-Metric-Space M U y}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M U)
            ( v)}
          ( ιx~κu)
          ( ιy~κv)
          ( d)
          ( preserves-neighborhoods-map-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M U))
            ( isometry-cauchy-pseudocompletion-extension-Metric-Space M U)
            ( d)
            ( x)
            ( y)
            ( N[u][v] (x , x∈[u]) (y , y∈[v]))))

  is-isometry-map-cauchy-precompletion-is-cauchy-dense-extentions-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( cauchy-precompletion-Metric-Space M)
      ( map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( M)
        ( U)
        ( dense-U))
  is-isometry-map-cauchy-precompletion-is-cauchy-dense-extentions-Metric-Space
    d u v =
    ( ( preserves-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( d)
        ( u)
        ( v)) ,
      ( reflects-neighborhoods-map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
        ( d)
        ( u)
        ( v)))
```

#### The isometry from a Cauchy-dense extension into the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (dense-U : is-cauchy-dense-extension-Metric-Space M U)
  where

  isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( cauchy-precompletion-Metric-Space M)
  pr1 isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space =
    map-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space M U dense-U
  pr2 isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space =
    is-isometry-map-cauchy-precompletion-is-cauchy-dense-extentions-Metric-Space
      ( M)
      ( U)
      ( dense-U)
```

#### The extension from a Cauchy-dense extension into the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (dense-U : is-cauchy-dense-extension-Metric-Space M U)
  where

  extension-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space :
    extension-Metric-Space
      ( l1 ⊔ l2)
      ( l1 ⊔ l2)
      ( metric-space-extension-Metric-Space M U)
  pr1 extension-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space =
    cauchy-precompletion-Metric-Space M
  pr2 extension-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space =
    isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
      ( M)
      ( U)
      ( dense-U)
```
