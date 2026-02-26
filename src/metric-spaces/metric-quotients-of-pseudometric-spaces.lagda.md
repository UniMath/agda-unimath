# Metric quotients of pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-quotients-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
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
and [neighborhoods](metric-spaces.rational-neighborhood-relations.md) are
neighborhoods of inhabitants of the quotient classes: two quotient classes `X`,
`Y` are in a `d`-neighborhood if for all `x ∈ X` and `y ∈ Y`, `x` and `y` are
`d`-neighbors in the pseudometric space.

## Definitions

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
        ( pseudometric-metric-quotient-Pseudometric-Space M)
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

## See also

- The
  [unit map](metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces.md)
  from a pseudometric space into its metric quotient;
- the
  [universal property of metric quotients and short maps](metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces.md);
- the
  [universal property of metric quotients and isometries](metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces.md).

## External links

- [Metric identification](https://en.wikipedia.org/wiki/Pseudometric_space#Metric_identification)
  on pseudometric spaces at Wikipedia
