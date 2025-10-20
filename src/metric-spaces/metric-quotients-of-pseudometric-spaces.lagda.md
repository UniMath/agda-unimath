# Metric quotients of pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-quotients-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retractions
open import foundation.sections
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-completion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "metric quotient" Disambiguation="of a pseudometric space" Agda=metric-quotient-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is the
[metric space](metric-spaces.metric-spaces.md) whose points are
[quotient classes](foundation.set-quotients.md) of `M` by the
[similarity relation](metric-spaces.similarity-of-elements-pseudometric-spaces.md)
and [neighborhoods](metric-spaces.rational-neighborhood-relations.md) given by
neighborhoods of inhabitants of the quotient classes: two quotient classes `X`,
`Y` are in a `d`-neighborhood if for all `x ∈ X` and `y ∈ Y`, `x` and `y` are
`d`-neighbors in the pseudometric space.

Any metric space is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to the
metric quotient of its underlying pseudometric space.

## Definition

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  set-metric-quotient-Pseudometric-Space : Set (l1 ⊔ l2)
  set-metric-quotient-Pseudometric-Space =
    quotient-Set (equivalence-relation-sim-Pseudometric-Space M)

  type-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2)
  type-metric-quotient-Pseudometric-Space =
    type-Set set-metric-quotient-Pseudometric-Space

  subtype-class-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space) →
    subtype l2 (type-Pseudometric-Space M)
  subtype-class-metric-quotient-Pseudometric-Space =
    subtype-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)

  is-in-class-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space) →
    type-Pseudometric-Space M →
    UU l2
  is-in-class-metric-quotient-Pseudometric-Space =
    is-in-equivalence-class-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)

  type-subtype-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space) → UU (l1 ⊔ l2)
  type-subtype-metric-quotient-Pseudometric-Space X =
    type-subtype
      ( subtype-class-metric-quotient-Pseudometric-Space X)

  neighborhood-prop-metric-quotient-Pseudometric-Space :
    Rational-Neighborhood-Relation
      ( l1 ⊔ l2)
      ( type-metric-quotient-Pseudometric-Space)
  neighborhood-prop-metric-quotient-Pseudometric-Space ε X Y =
    Π-Prop
      ( type-subtype-metric-quotient-Pseudometric-Space X)
      ( λ (x , x∈X) →
        Π-Prop
          ( type-subtype-metric-quotient-Pseudometric-Space Y)
          ( λ (y , y∈Y) → neighborhood-prop-Pseudometric-Space M ε x y))

  neighborhood-metric-quotient-Pseudometric-Space :
    ℚ⁺ → Relation (l1 ⊔ l2) type-metric-quotient-Pseudometric-Space
  neighborhood-metric-quotient-Pseudometric-Space ε X Y =
    type-Prop (neighborhood-prop-metric-quotient-Pseudometric-Space ε X Y)
```

## Properties

### All quotient classes are inhabited

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (x : type-metric-quotient-Pseudometric-Space A)
  where

  is-inhabited-class-metric-quotient-Pseudometric-Space :
    is-inhabited-subtype
      ( subtype-class-metric-quotient-Pseudometric-Space A x)
  is-inhabited-class-metric-quotient-Pseudometric-Space =
    is-inhabited-subtype-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( x)
```

### The quotient neighborhood relation is reflexive

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-reflexive-neighborhood-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) (X : type-metric-quotient-Pseudometric-Space M) →
      neighborhood-metric-quotient-Pseudometric-Space M d X X
    is-reflexive-neighborhood-metric-quotient-Pseudometric-Space
      d X (x , x∈X) (y , y∈X) =
      apply-effectiveness-quotient-map
        ( equivalence-relation-sim-Pseudometric-Space M)
        ( ( eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( X)
            ( x∈X)) ∙
          ( inv
            ( eq-set-quotient-equivalence-class-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space M)
              ( X)
              ( y∈X))))
        ( d)
```

### The quotient neighborhood relation is symmetric

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-symmetric-neighborhood-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-metric-quotient-Pseudometric-Space M) →
      neighborhood-metric-quotient-Pseudometric-Space M d x y →
      neighborhood-metric-quotient-Pseudometric-Space M d y x
    is-symmetric-neighborhood-metric-quotient-Pseudometric-Space
      d X Y d⟨X,Y⟩ (y , y∈Y) (x , x∈X) =
      symmetric-neighborhood-Pseudometric-Space
        ( M)
        ( d)
        ( x)
        ( y)
        ( d⟨X,Y⟩ (x , x∈X) (y , y∈Y))
```

### The quotient neighborhood relation is triangular

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  (X Y Z : type-metric-quotient-Pseudometric-Space M)
  (d₁ d₂ : ℚ⁺)
  where

  abstract
    is-triangular-neighborhood-metric-quotient-Pseudometric-Space :
      neighborhood-metric-quotient-Pseudometric-Space M d₂ Y Z →
      neighborhood-metric-quotient-Pseudometric-Space M d₁ X Y →
      neighborhood-metric-quotient-Pseudometric-Space M (d₁ +ℚ⁺ d₂) X Z
    is-triangular-neighborhood-metric-quotient-Pseudometric-Space
      d₂⟨Y,Z⟩ d₁⟨X,Y⟩ (x , x∈X) (z , z∈Z) =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Pseudometric-Space M (d₁ +ℚ⁺ d₂) x z)
      in do
        (y , y∈Y) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( Y)
        triangular-neighborhood-Pseudometric-Space
          ( M)
          ( x)
          ( y)
          ( z)
          ( d₁)
          ( d₂)
          ( d₂⟨Y,Z⟩ (y , y∈Y) (z , z∈Z))
          ( d₁⟨X,Y⟩ (x , x∈X) (y , y∈Y))
```

### The quotient neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-saturated-neighborhood-metric-quotient-Pseudometric-Space :
      (ε : ℚ⁺) (X Y : type-metric-quotient-Pseudometric-Space M) →
      ((δ : ℚ⁺) →
        neighborhood-metric-quotient-Pseudometric-Space M (ε +ℚ⁺ δ) X Y) →
      neighborhood-metric-quotient-Pseudometric-Space M ε X Y
    is-saturated-neighborhood-metric-quotient-Pseudometric-Space
      ε X Y H (x , x∈X) (y , y∈Y) =
      saturated-neighborhood-Pseudometric-Space M ε x y
        ( λ δ → H δ (x , x∈X) (y , y∈Y))
```

### The quotient pseudometric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  pseudometric-metric-quotient-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-metric-quotient-Pseudometric-Space =
    ( type-metric-quotient-Pseudometric-Space M ,
      neighborhood-prop-metric-quotient-Pseudometric-Space M ,
      is-reflexive-neighborhood-metric-quotient-Pseudometric-Space M ,
      is-symmetric-neighborhood-metric-quotient-Pseudometric-Space M ,
      is-triangular-neighborhood-metric-quotient-Pseudometric-Space M ,
      is-saturated-neighborhood-metric-quotient-Pseudometric-Space M)
```

### The quotient pseudometric space is tight and extensional

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-tight-pseudometric-metric-quotient-Pseudometric-Space :
      is-tight-Pseudometric-Space
        (pseudometric-metric-quotient-Pseudometric-Space M)
    is-tight-pseudometric-metric-quotient-Pseudometric-Space X Y X~Y =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-metric-quotient-Pseudometric-Space M)
              ( X)
              ( Y))
      in do
        ( x , x∈X) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( X)

        ( y , y∈Y) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( Y)

        eq-set-quotient-sim-element-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space M)
          ( X)
          ( Y)
          ( x∈X)
          ( y∈Y)
          ( λ d → X~Y d (x , x∈X) (y , y∈Y))

    is-extensional-pseudometric-metric-quotient-Pseudometric-Space :
      is-extensional-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space M)
    is-extensional-pseudometric-metric-quotient-Pseudometric-Space =
      is-extensional-is-tight-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space M)
        ( is-tight-pseudometric-metric-quotient-Pseudometric-Space)
```

### The quotient metric space of a pseudometric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  metric-quotient-Pseudometric-Space : Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-quotient-Pseudometric-Space =
    make-Metric-Space
      ( type-metric-quotient-Pseudometric-Space M)
      ( neighborhood-prop-metric-quotient-Pseudometric-Space M)
      ( is-reflexive-neighborhood-metric-quotient-Pseudometric-Space M)
      ( is-symmetric-neighborhood-metric-quotient-Pseudometric-Space M)
      ( is-triangular-neighborhood-metric-quotient-Pseudometric-Space M)
      ( is-saturated-neighborhood-metric-quotient-Pseudometric-Space M)
      ( is-extensional-pseudometric-metric-quotient-Pseudometric-Space M)
```

### The mapping from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  map-metric-quotient-Pseudometric-Space :
    type-Pseudometric-Space M → type-metric-quotient-Pseudometric-Space M
  map-metric-quotient-Pseudometric-Space =
    quotient-map (equivalence-relation-sim-Pseudometric-Space M)

  is-in-class-map-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( M)
      ( map-metric-quotient-Pseudometric-Space x)
      ( x)
  is-in-class-map-quotient-Pseudometric-Space =
    is-in-equivalence-class-quotient-map-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)

  map-subtype-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    type-subtype-metric-quotient-Pseudometric-Space M
      ( map-metric-quotient-Pseudometric-Space x)
  map-subtype-metric-quotient-Pseudometric-Space =
    inhabitant-equivalence-class-quotient-map-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)
```

### The mapping from a pseudometric space its quotient metric space is an isometry

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    preserves-neighborhood-map-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-Pseudometric-Space M d x y →
      neighborhood-metric-quotient-Pseudometric-Space
        ( M)
        ( d)
        ( map-metric-quotient-Pseudometric-Space M x)
        ( map-metric-quotient-Pseudometric-Space M y)
    preserves-neighborhood-map-metric-quotient-Pseudometric-Space
      d x y d⟨x,y⟩ (x' , x≈x') (y' , y≈y') =
      let
        x~x' =
          sim-is-in-equivalence-class-quotient-map-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( x)
            ( x')
            ( x≈x')

        y~y' =
          sim-is-in-equivalence-class-quotient-map-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( y)
            ( y')
            ( y≈y')

      in
        preserves-neighborhood-right-sim-Pseudometric-Space M y~y' d x'
          ( preserves-neighborhood-left-sim-Pseudometric-Space
            ( M)
            ( x~x')
            ( d)
            ( y)
            ( d⟨x,y⟩))

    reflects-neighborhood-map-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-metric-quotient-Pseudometric-Space
        ( M)
        ( d)
        ( map-metric-quotient-Pseudometric-Space M x)
        ( map-metric-quotient-Pseudometric-Space M y) →
      neighborhood-Pseudometric-Space M d x y
    reflects-neighborhood-map-metric-quotient-Pseudometric-Space
      d x y Nxy =
        Nxy
          ( map-subtype-metric-quotient-Pseudometric-Space M x)
          ( map-subtype-metric-quotient-Pseudometric-Space M y)

  is-isometry-map-metric-quotient-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
      ( map-metric-quotient-Pseudometric-Space M)
  is-isometry-map-metric-quotient-Pseudometric-Space d x y =
    ( preserves-neighborhood-map-metric-quotient-Pseudometric-Space d x y ,
      reflects-neighborhood-map-metric-quotient-Pseudometric-Space d x y)
```

### The isometry from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  isometry-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
  isometry-metric-quotient-Pseudometric-Space =
    ( map-metric-quotient-Pseudometric-Space M ,
      is-isometry-map-metric-quotient-Pseudometric-Space M)
```

### The short map from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  short-map-metric-quotient-Pseudometric-Space :
    short-function-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
  short-map-metric-quotient-Pseudometric-Space =
    short-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
      ( isometry-metric-quotient-Pseudometric-Space M)
```

### The isometric equivalence between a metric space and the quotient metric space of its pseudometric space

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  map-metric-quotient-Metric-Space :
    type-Metric-Space M →
    type-metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space M)
  map-metric-quotient-Metric-Space =
    map-metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  abstract
    is-contr-map-metric-quotient-Metric-Space :
      is-contr-map map-metric-quotient-Metric-Space
    is-contr-map-metric-quotient-Metric-Space X =
      let
        open
          do-syntax-trunc-Prop
            ( is-contr-Prop
              ( fiber map-metric-quotient-Metric-Space X))
        in do
          ( x , x∈X) ←
            is-inhabited-subtype-set-quotient
              ( equivalence-relation-sim-Metric-Space M)
              ( X)

          ( ( x ,
              eq-set-quotient-equivalence-class-set-quotient
                ( equivalence-relation-sim-Metric-Space M)
                ( X)
                ( x∈X)) ,
            ( λ (y , Y＝X) →
              eq-type-subtype
                ( λ z →
                  Id-Prop
                    ( set-metric-quotient-Pseudometric-Space
                      ( pseudometric-Metric-Space M))
                      ( map-metric-quotient-Metric-Space z)
                      ( X))
                ( eq-sim-Metric-Space
                  ( M)
                  ( x)
                  ( y)
                  ( apply-effectiveness-quotient-map
                    ( equivalence-relation-sim-Metric-Space M)
                    ( ( eq-set-quotient-equivalence-class-set-quotient
                        ( equivalence-relation-sim-Metric-Space M)
                        ( X)
                        ( x∈X)) ∙
                      ( inv Y＝X))))))

    is-equiv-map-metric-quotient-Metric-Space :
      is-equiv map-metric-quotient-Metric-Space
    is-equiv-map-metric-quotient-Metric-Space =
      is-equiv-is-contr-map
        ( is-contr-map-metric-quotient-Metric-Space)

    is-isometry-map-metric-quotient-Metric-Space :
      is-isometry-Metric-Space
        ( M)
        ( metric-quotient-Pseudometric-Space
          ( pseudometric-Metric-Space M))
        ( map-metric-quotient-Metric-Space)
    is-isometry-map-metric-quotient-Metric-Space =
      is-isometry-map-metric-quotient-Pseudometric-Space
        ( pseudometric-Metric-Space M)

  isometric-equiv-metric-quotient-Metric-Space' :
    isometric-equiv-Metric-Space'
      ( M)
      ( metric-quotient-Pseudometric-Space
        ( pseudometric-Metric-Space M))
  isometric-equiv-metric-quotient-Metric-Space' =
    ( map-metric-quotient-Metric-Space ,
      is-equiv-map-metric-quotient-Metric-Space ,
      is-isometry-map-metric-quotient-Metric-Space)
```

### The construction of the quotient metric space of a pseudometric space is idempotent

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-idempotent-metric-quotient-Pseudometric-Space :
    metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( metric-quotient-Pseudometric-Space M)) ＝
    metric-quotient-Pseudometric-Space M
  is-idempotent-metric-quotient-Pseudometric-Space =
    inv
      ( eq-isometric-equiv-Metric-Space'
        ( metric-quotient-Pseudometric-Space M)
        ( metric-quotient-Pseudometric-Space
          ( pseudometric-Metric-Space
            ( metric-quotient-Pseudometric-Space M)))
        ( isometric-equiv-metric-quotient-Metric-Space'
          ( metric-quotient-Pseudometric-Space M)))
```

### Characterization of functions from the quotient metric space into metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2)
  (B : Metric-Space l1' l2')
  where

  precomp-map-metric-quotient-Pseudometric-Space :
    type-function-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B) →
    reflecting-map-equivalence-relation
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( type-Metric-Space B)
  precomp-map-metric-quotient-Pseudometric-Space =
    precomp-Set-Quotient
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( set-metric-quotient-Pseudometric-Space A)
      ( reflecting-map-quotient-map
        ( equivalence-relation-sim-Pseudometric-Space A))
      ( set-Metric-Space B)

  is-equiv-precomp-map-metric-quotient-Pseudometric-Space :
    is-equiv precomp-map-metric-quotient-Pseudometric-Space
  is-equiv-precomp-map-metric-quotient-Pseudometric-Space =
    is-set-quotient-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( set-Metric-Space B)

  equiv-type-function-metric-quotient-Pseudometric-Space :
    type-function-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B) ≃
    reflecting-map-equivalence-relation
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( type-Metric-Space B)
  equiv-type-function-metric-quotient-Pseudometric-Space =
    ( precomp-map-metric-quotient-Pseudometric-Space ,
      is-equiv-precomp-map-metric-quotient-Pseudometric-Space)
```

### Induced short function from the quotient metric space into a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2)
  (B : Metric-Space l1' l2')
  (f : short-function-Pseudometric-Space A (pseudometric-Metric-Space B))
  where

  map-short-function-metric-quotient-Pseudometric-space :
    type-function-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  map-short-function-metric-quotient-Pseudometric-space =
    inv-precomp-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( set-Metric-Space B)
      ( reflecting-map-short-function-metric-space-Pseudometric-Space A B f)

  htpy-map-short-function-metric-quotient-Pseudometric-Space :
    ( ( map-short-function-metric-quotient-Pseudometric-space) ∘
      ( map-metric-quotient-Pseudometric-Space A)) ~
    ( map-short-function-Pseudometric-Space A (pseudometric-Metric-Space B) f)
  htpy-map-short-function-metric-quotient-Pseudometric-Space =
    is-section-inv-precomp-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space A)
      ( set-Metric-Space B)
      ( reflecting-map-short-function-metric-space-Pseudometric-Space A B f)

  compute-map-short-function-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space A) →
    (x : type-Pseudometric-Space A) →
    is-in-class-metric-quotient-Pseudometric-Space A X x →
    map-short-function-metric-quotient-Pseudometric-space X ＝
    map-short-function-Pseudometric-Space A (pseudometric-Metric-Space B) f x
  compute-map-short-function-metric-quotient-Pseudometric-Space X x x∈X =
    tr
      ( λ Y →
        map-short-function-metric-quotient-Pseudometric-space Y ＝
        map-short-function-Pseudometric-Space
          ( A)
          ( pseudometric-Metric-Space B)
          ( f)
          ( x))
      ( eq-set-quotient-equivalence-class-set-quotient
        ( equivalence-relation-sim-Pseudometric-Space A)
        ( X)
        ( x∈X))
      ( htpy-map-short-function-metric-quotient-Pseudometric-Space x)

  abstract
    is-short-map-short-function-metric-quotient-Pseudometric-Space :
      is-short-function-Metric-Space
        ( metric-quotient-Pseudometric-Space A)
        ( B)
        ( map-short-function-metric-quotient-Pseudometric-space)
    is-short-map-short-function-metric-quotient-Pseudometric-Space
      d X Y N⟨X,Y⟩ =
      let
        open
          do-syntax-trunc-Prop
            ( neighborhood-prop-Metric-Space
              ( B)
              ( d)
              ( map-short-function-metric-quotient-Pseudometric-space X)
              ( map-short-function-metric-quotient-Pseudometric-space Y))
        in do
          ( x , x∈X) ←
            is-inhabited-subtype-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space A)
              ( X)
          ( y , y∈Y) ←
            is-inhabited-subtype-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space A)
              ( Y)

          binary-tr
            ( neighborhood-Metric-Space B d)
            ( inv
              ( compute-map-short-function-metric-quotient-Pseudometric-Space
                ( X)
                ( x)
                ( x∈X)))
            ( inv
              ( compute-map-short-function-metric-quotient-Pseudometric-Space
                ( Y)
                ( y)
                ( y∈Y)))
            ( is-short-map-short-function-Pseudometric-Space
              ( A)
              ( pseudometric-Metric-Space B)
              ( f)
              ( d)
              ( x)
              ( y)
              ( N⟨X,Y⟩ (x , x∈X) (y , y∈Y)))

  short-map-short-function-metric-quotient-Pseudometric-Space :
    short-function-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  short-map-short-function-metric-quotient-Pseudometric-Space =
    ( map-short-function-metric-quotient-Pseudometric-space ,
      is-short-map-short-function-metric-quotient-Pseudometric-Space)
```

### Induced isometry from the quotient metric space into a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2)
  (B : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space A (pseudometric-Metric-Space B))
  where

  map-isometry-metric-quotient-Pseudometric-Space :
    type-function-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  map-isometry-metric-quotient-Pseudometric-Space =
    map-short-function-metric-quotient-Pseudometric-space
      ( A)
      ( B)
      ( short-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  htpy-map-isometry-metric-quotient-Pseudometric-Space :
    ( ( map-isometry-metric-quotient-Pseudometric-Space) ∘
      ( map-metric-quotient-Pseudometric-Space A)) ~
    ( map-isometry-Pseudometric-Space A (pseudometric-Metric-Space B) f)
  htpy-map-isometry-metric-quotient-Pseudometric-Space =
    htpy-map-short-function-metric-quotient-Pseudometric-Space
      ( A)
      ( B)
      ( short-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  compute-map-isometry-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space A) →
    (x : type-Pseudometric-Space A) →
    is-in-class-metric-quotient-Pseudometric-Space A X x →
    map-isometry-metric-quotient-Pseudometric-Space X ＝
    map-isometry-Pseudometric-Space
      ( A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( x)
  compute-map-isometry-metric-quotient-Pseudometric-Space =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( A)
      ( B)
      ( short-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  abstract
    preserves-neighborhood-map-isometry-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) →
      (x y : type-metric-quotient-Pseudometric-Space A) →
      neighborhood-metric-quotient-Pseudometric-Space
        ( A)
        ( d)
        ( x)
        ( y) →
      neighborhood-Metric-Space
        ( B)
        ( d)
        ( map-isometry-metric-quotient-Pseudometric-Space x)
        ( map-isometry-metric-quotient-Pseudometric-Space y)
    preserves-neighborhood-map-isometry-metric-quotient-Pseudometric-Space =
      is-short-map-short-function-metric-quotient-Pseudometric-Space
        ( A)
        ( B)
        ( short-isometry-Pseudometric-Space
          ( A)
          ( pseudometric-Metric-Space B)
          ( f))

    reflects-neighborhood-map-isometry-metric-quotient-Pseudometric-Space :
      (d : ℚ⁺) →
      (x y : type-metric-quotient-Pseudometric-Space A) →
      neighborhood-Metric-Space
        ( B)
        ( d)
        ( map-isometry-metric-quotient-Pseudometric-Space x)
        ( map-isometry-metric-quotient-Pseudometric-Space y) →
      neighborhood-metric-quotient-Pseudometric-Space
        ( A)
        ( d)
        ( x)
        ( y)
    reflects-neighborhood-map-isometry-metric-quotient-Pseudometric-Space
      d X Y N⟨fX,fY⟩ (x , x∈X) (y , y∈Y) =
      reflects-neighborhood-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f)
        ( d)
        ( x)
        ( y)
        ( binary-tr
          ( neighborhood-Metric-Space B d)
          ( compute-map-isometry-metric-quotient-Pseudometric-Space X x x∈X)
          ( compute-map-isometry-metric-quotient-Pseudometric-Space Y y y∈Y)
          ( N⟨fX,fY⟩))

    is-isometry-map-isometry-metric-quotient-Pseudometric-Space :
      is-isometry-Metric-Space
        ( metric-quotient-Pseudometric-Space A)
        ( B)
        ( map-isometry-metric-quotient-Pseudometric-Space)
    is-isometry-map-isometry-metric-quotient-Pseudometric-Space d x y =
      ( preserves-neighborhood-map-isometry-metric-quotient-Pseudometric-Space
        ( d)
        ( x)
        ( y) ,
        reflects-neighborhood-map-isometry-metric-quotient-Pseudometric-Space
          ( d)
          ( x)
          ( y))

  isometry-map-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  isometry-map-isometry-metric-quotient-Pseudometric-Space =
    ( map-isometry-metric-quotient-Pseudometric-Space ,
      is-isometry-map-isometry-metric-quotient-Pseudometric-Space)
```

## External links

- [Metric identification](https://en.wikipedia.org/wiki/Pseudometric_space#Metric_identification)
  on pseudometric spaces at Wikipedia
