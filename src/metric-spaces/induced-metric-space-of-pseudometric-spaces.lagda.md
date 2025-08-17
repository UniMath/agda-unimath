# The induced metric space of a pseudometric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.induced-metric-space-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "induced metric space" Disambiguation="of a pseudometric space" Agda=induced-metric-space-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is the
[metric space](metric-spaces.metric-spaces.lagda.md) whose points are
[quotient classes](foundation.set-quotients.md) of `M` by the
[similarity relation](metric-spaces.similarity-of-elements-pseudometric-spaces.md).
and [neighborhoods](metric-spaces.rational-neighborhood-relations.md) given by
neighborhoods of inhabitants of the quotient classes: two quotient classes `X`,
`Y` are in a `d`-neighborhood if for all `x ∈ X` and `y ∈ Y`, `x` and `y` are
`d`-neighbors in the pseudometric space.

Any metric space is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to its
induced metric space.

## Definition

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  set-induced-metric-space-Pseudometric-Space : Set (l1 ⊔ l2)
  set-induced-metric-space-Pseudometric-Space =
    quotient-Set (equivalence-relation-sim-Pseudometric-Space M)

  type-induced-metric-space-Pseudometric-Space : UU (l1 ⊔ l2)
  type-induced-metric-space-Pseudometric-Space =
    type-Set set-induced-metric-space-Pseudometric-Space

  type-subtype-induced-metric-space-Pseudometric-Space :
    (X : type-induced-metric-space-Pseudometric-Space) → UU (l1 ⊔ l2)
  type-subtype-induced-metric-space-Pseudometric-Space X =
    type-subtype
      ( subtype-set-quotient
        ( equivalence-relation-sim-Pseudometric-Space M)
        ( X))

  neighborhood-prop-induced-metric-space-Pseudometric-Space :
    Rational-Neighborhood-Relation
      ( l1 ⊔ l2)
      ( type-induced-metric-space-Pseudometric-Space)
  neighborhood-prop-induced-metric-space-Pseudometric-Space ε X Y =
    Π-Prop
      ( type-subtype-induced-metric-space-Pseudometric-Space X)
      ( λ (x , x∈X) →
        Π-Prop
          ( type-subtype-induced-metric-space-Pseudometric-Space Y)
          ( λ (y , y∈Y) → neighborhood-prop-Pseudometric-Space M ε x y))

  neighborhood-induced-metric-space-Pseudometric-Space :
    ℚ⁺ → Relation (l1 ⊔ l2) type-induced-metric-space-Pseudometric-Space
  neighborhood-induced-metric-space-Pseudometric-Space ε X Y =
    type-Prop (neighborhood-prop-induced-metric-space-Pseudometric-Space ε X Y)
```

## Properties

### The induced neighborhood relation is reflexive

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-reflexive-neighborhood-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (X : type-induced-metric-space-Pseudometric-Space M) →
      neighborhood-induced-metric-space-Pseudometric-Space M d X X
    is-reflexive-neighborhood-induced-metric-space-Pseudometric-Space
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

### The induced neighborhood relation is symmetric

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-symmetric-neighborhood-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-induced-metric-space-Pseudometric-Space M) →
      neighborhood-induced-metric-space-Pseudometric-Space M d x y →
      neighborhood-induced-metric-space-Pseudometric-Space M d y x
    is-symmetric-neighborhood-induced-metric-space-Pseudometric-Space
      d X Y d⟨X,Y⟩ (y , y∈Y) (x , x∈X) =
      symmetric-neighborhood-Pseudometric-Space
        ( M)
        ( d)
        ( x)
        ( y)
        ( d⟨X,Y⟩ (x , x∈X) (y , y∈Y))
```

### The induced neighborhood relation is triangular

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  (X Y Z : type-induced-metric-space-Pseudometric-Space M)
  (d₁ d₂ : ℚ⁺)
  where

  abstract
    is-triangular-neighborhood-induced-metric-space-Pseudometric-Space :
      neighborhood-induced-metric-space-Pseudometric-Space M d₂ Y Z →
      neighborhood-induced-metric-space-Pseudometric-Space M d₁ X Y →
      neighborhood-induced-metric-space-Pseudometric-Space M (d₁ +ℚ⁺ d₂) X Z
    is-triangular-neighborhood-induced-metric-space-Pseudometric-Space
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

### The induced neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-saturated-neighborhood-induced-metric-space-Pseudometric-Space :
      (ε : ℚ⁺) (X Y : type-induced-metric-space-Pseudometric-Space M) →
      ((δ : ℚ⁺) →
        neighborhood-induced-metric-space-Pseudometric-Space M (ε +ℚ⁺ δ) X Y) →
      neighborhood-induced-metric-space-Pseudometric-Space M ε X Y
    is-saturated-neighborhood-induced-metric-space-Pseudometric-Space
      ε X Y H (x , x∈X) (y , y∈Y) =
      saturated-neighborhood-Pseudometric-Space M ε x y
        ( λ δ → H δ (x , x∈X) (y , y∈Y))
```

### The induced pseudometric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  pseudometric-induced-metric-space-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-induced-metric-space-Pseudometric-Space =
    ( type-induced-metric-space-Pseudometric-Space M ,
      neighborhood-prop-induced-metric-space-Pseudometric-Space M ,
      is-reflexive-neighborhood-induced-metric-space-Pseudometric-Space M ,
      is-symmetric-neighborhood-induced-metric-space-Pseudometric-Space M ,
      is-triangular-neighborhood-induced-metric-space-Pseudometric-Space M ,
      is-saturated-neighborhood-induced-metric-space-Pseudometric-Space M)
```

### The induced pseudometric is tight and extensional

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-tight-pseudometric-induced-metric-space-Pseudometric-Space :
      is-tight-Pseudometric-Space
        (pseudometric-induced-metric-space-Pseudometric-Space M)
    is-tight-pseudometric-induced-metric-space-Pseudometric-Space X Y X~Y =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-induced-metric-space-Pseudometric-Space M)
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

    is-extensional-pseudometric-induced-metric-space-Pseudometric-Space :
      is-extensional-Pseudometric-Space
        ( pseudometric-induced-metric-space-Pseudometric-Space M)
    is-extensional-pseudometric-induced-metric-space-Pseudometric-Space =
      is-extensional-is-tight-Pseudometric-Space
        ( pseudometric-induced-metric-space-Pseudometric-Space M)
        ( is-tight-pseudometric-induced-metric-space-Pseudometric-Space)
```

### The induced metric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  induced-metric-space-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  induced-metric-space-Pseudometric-Space =
    make-Metric-Space
      ( type-induced-metric-space-Pseudometric-Space M)
      ( neighborhood-prop-induced-metric-space-Pseudometric-Space M)
      ( is-reflexive-neighborhood-induced-metric-space-Pseudometric-Space M)
      ( is-symmetric-neighborhood-induced-metric-space-Pseudometric-Space M)
      ( is-triangular-neighborhood-induced-metric-space-Pseudometric-Space M)
      ( is-saturated-neighborhood-induced-metric-space-Pseudometric-Space M)
      ( is-extensional-pseudometric-induced-metric-space-Pseudometric-Space M)
```

### Mapping from the pseudometric space to the induced metric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  map-induced-metric-space-Pseudometric-Space :
    type-Pseudometric-Space M → type-induced-metric-space-Pseudometric-Space M
  map-induced-metric-space-Pseudometric-Space =
    quotient-map (equivalence-relation-sim-Pseudometric-Space M)

  map-subtype-induced-metric-space-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    type-subtype-induced-metric-space-Pseudometric-Space M
      ( map-induced-metric-space-Pseudometric-Space x)
  map-subtype-induced-metric-space-Pseudometric-Space =
    inhabitant-equivalence-class-quotient-map-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)
```

### The mapping from the pseudometric space to the induced metric space is an isometry

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  abstract
    preserves-neighborhood-map-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-Pseudometric-Space M d x y →
      neighborhood-induced-metric-space-Pseudometric-Space
        ( M)
        ( d)
        ( map-induced-metric-space-Pseudometric-Space M x)
        ( map-induced-metric-space-Pseudometric-Space M y)
    preserves-neighborhood-map-induced-metric-space-Pseudometric-Space
      d x y d⟨x,y⟩ (x' , x≈x') (y' , y≈y') =
      let
        x~x' =
          sim-is-in-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( x)
            ( x')
            ( x≈x')

        y~y' =
          sim-is-in-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space M)
            ( y)
            ( y')
            ( y≈y')

      in
        preserves-neighborhood-sim-Pseudometric-Space' M y~y' d x'
          ( preserves-neighborhood-sim-Pseudometric-Space M x~x' d y d⟨x,y⟩)

    reflects-neighborhood-map-induced-metric-space-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-induced-metric-space-Pseudometric-Space
        ( M)
        ( d)
        ( map-induced-metric-space-Pseudometric-Space M x)
        ( map-induced-metric-space-Pseudometric-Space M y) →
      neighborhood-Pseudometric-Space M d x y
    reflects-neighborhood-map-induced-metric-space-Pseudometric-Space
      d x y Nxy =
        Nxy
          ( map-subtype-induced-metric-space-Pseudometric-Space M x)
          ( map-subtype-induced-metric-space-Pseudometric-Space M y)

  is-isometry-map-induced-metric-space-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-induced-metric-space-Pseudometric-Space M)
      ( map-induced-metric-space-Pseudometric-Space M)
  is-isometry-map-induced-metric-space-Pseudometric-Space d x y =
    ( preserves-neighborhood-map-induced-metric-space-Pseudometric-Space d x y ,
      reflects-neighborhood-map-induced-metric-space-Pseudometric-Space d x y)
```

### The isometry from a pseudometric space to its induced metric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  isometry-map-induced-metric-space-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( M)
      ( pseudometric-induced-metric-space-Pseudometric-Space M)
  isometry-map-induced-metric-space-Pseudometric-Space =
    ( map-induced-metric-space-Pseudometric-Space M ,
      is-isometry-map-induced-metric-space-Pseudometric-Space M)
```

### The isometric equivalence between a metric space and the induced metric space of its pseudometric

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  map-induced-metric-space-Metric-Space :
    type-Metric-Space M →
    type-induced-metric-space-Pseudometric-Space
      ( pseudometric-Metric-Space M)
  map-induced-metric-space-Metric-Space =
    map-induced-metric-space-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  abstract
    is-contr-map-induced-metric-space-Metric-Space :
      is-contr-map map-induced-metric-space-Metric-Space
    is-contr-map-induced-metric-space-Metric-Space X =
      let
        open
          do-syntax-trunc-Prop
            ( is-contr-Prop
              ( fiber map-induced-metric-space-Metric-Space X))
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
                    ( set-induced-metric-space-Pseudometric-Space
                      ( pseudometric-Metric-Space M))
                      ( map-induced-metric-space-Metric-Space z)
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

    is-equiv-map-induced-metric-space-Metric-Space :
      is-equiv map-induced-metric-space-Metric-Space
    is-equiv-map-induced-metric-space-Metric-Space =
      is-equiv-is-contr-map
        ( is-contr-map-induced-metric-space-Metric-Space)

    is-isometry-map-induced-metric-space-Metric-Space :
      is-isometry-Metric-Space
        ( M)
        ( induced-metric-space-Pseudometric-Space
          ( pseudometric-Metric-Space M))
        ( map-induced-metric-space-Metric-Space)
    is-isometry-map-induced-metric-space-Metric-Space =
      is-isometry-map-induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M)

  isometric-equiv-induced-metric-space-Metric-Space' :
    isometric-equiv-Metric-Space'
      ( M)
      ( induced-metric-space-Pseudometric-Space
        ( pseudometric-Metric-Space M))
  isometric-equiv-induced-metric-space-Metric-Space' =
    ( map-induced-metric-space-Metric-Space ,
      is-equiv-map-induced-metric-space-Metric-Space ,
      is-isometry-map-induced-metric-space-Metric-Space)
```
