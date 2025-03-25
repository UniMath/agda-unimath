# Discrete premetric structures

```agda
module metric-spaces.discrete-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

Any type comes equipped with a canonical
{{#concept "discrete" Disambiguation="premetric structure" Agda=is-discrete-Premetric}}
[premetric](metric-spaces.premetric-structures.md) where `d`-neighbors are
[merely equal](foundation.mere-equality.md) elements. This is the unique
reflexive premetric such that two points are at bounded distance if and only if
they are merely equal, in which case they are indistinguishable.

## Definitions

### The property of being a semidiscrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-semidiscrete-prop-Premetric : Prop (l1 ⊔ l2)
  is-semidiscrete-prop-Premetric =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y →
                hom-Prop
                  ( B d x y)
                  ( trunc-Prop (x ＝ y)))))

  is-semidiscrete-Premetric : UU (l1 ⊔ l2)
  is-semidiscrete-Premetric = type-Prop is-semidiscrete-prop-Premetric

  is-prop-is-semidiscrete-Premetric : is-prop is-semidiscrete-Premetric
  is-prop-is-semidiscrete-Premetric =
    is-prop-type-Prop is-semidiscrete-prop-Premetric
```

### The property of being a discrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-discrete-prop-Premetric : Prop (l1 ⊔ l2)
  is-discrete-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( is-semidiscrete-prop-Premetric B)

  is-discrete-Premetric : UU (l1 ⊔ l2)
  is-discrete-Premetric = type-Prop is-discrete-prop-Premetric

  is-prop-is-discrete-Premetric : is-prop is-discrete-Premetric
  is-prop-is-discrete-Premetric =
    is-prop-type-Prop is-discrete-prop-Premetric
```

### The type of discrete premetrics on a type

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Discrete-Premetric : UU (l1 ⊔ lsuc l2)
  Discrete-Premetric = Σ (Premetric l2 A) is-discrete-Premetric
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Discrete-Premetric l2 A)
  where

  premetric-Discrete-Premetric : Premetric l2 A
  premetric-Discrete-Premetric = pr1 B

  is-discrete-premetric-Discrete-Premetric :
    is-discrete-Premetric premetric-Discrete-Premetric
  is-discrete-premetric-Discrete-Premetric = pr2 B

  is-reflexive-premetric-Discrete-Premetric :
    is-reflexive-Premetric premetric-Discrete-Premetric
  is-reflexive-premetric-Discrete-Premetric =
    pr1 is-discrete-premetric-Discrete-Premetric

  is-semidiscrete-premetric-Discrete-Premetric :
    is-semidiscrete-Premetric premetric-Discrete-Premetric
  is-semidiscrete-premetric-Discrete-Premetric =
    pr2 is-discrete-premetric-Discrete-Premetric
```

### The canonical discrete premetric on a type

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  premetric-discrete-Premetric : Premetric l1 A
  premetric-discrete-Premetric d x y = trunc-Prop (x ＝ y)

  is-discrete-premetric-discrete-Premetric :
    is-discrete-Premetric premetric-discrete-Premetric
  is-discrete-premetric-discrete-Premetric =
    (λ x d → unit-trunc-Prop refl) ,
    (λ d x y → id)

  discrete-Premetric : Discrete-Premetric l1 A
  discrete-Premetric =
    premetric-discrete-Premetric ,
    is-discrete-premetric-discrete-Premetric
```

## Properties

### Unicity of discrete premetric structures

#### Any discrete premetric on a type is equivalent to the canonical discrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Discrete-Premetric l2 A)
  (d : ℚ⁺) (x y : A)
  where

  iff-premetric-discrete-Discrete-Premetric :
    type-iff-Prop
      ( premetric-Discrete-Premetric B d x y)
      ( premetric-discrete-Premetric A d x y)
  iff-premetric-discrete-Discrete-Premetric =
    ( is-semidiscrete-premetric-Discrete-Premetric B d x y) ,
    ( rec-trunc-Prop
      ( premetric-Discrete-Premetric B d x y)
      ( λ e →
        indistinguishable-eq-reflexive-Premetric
          ( premetric-Discrete-Premetric B)
          ( is-reflexive-premetric-Discrete-Premetric B)
          ( e)
          ( d)))
```

#### Any two discrete premetrics on a type are equivalent

```agda
module _
  {la lb lc : Level} {A : UU la}
  (B : Discrete-Premetric lb A) (C : Discrete-Premetric lc A)
  (d : ℚ⁺) (x y : A)
  where

  iff-premetric-Discrete-Premetric :
    type-iff-Prop
      ( premetric-Discrete-Premetric B d x y)
      ( premetric-Discrete-Premetric C d x y)
  iff-premetric-Discrete-Premetric =
    ( inv-iff (iff-premetric-discrete-Discrete-Premetric C d x y)) ∘iff
    ( iff-premetric-discrete-Discrete-Premetric B d x y)
```

#### Any two discrete premetrics on a type are equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B B' : Discrete-Premetric l2 A)
  where

  all-elements-equal-Discrete-Premetric : B ＝ B'
  all-elements-equal-Discrete-Premetric =
    eq-type-subtype
      ( is-discrete-prop-Premetric)
      ( eq-Eq-Premetric
        ( premetric-Discrete-Premetric B)
        ( premetric-Discrete-Premetric B')
        ( iff-premetric-Discrete-Premetric B B'))
```

#### The type of discrete premetric structures on a type is a proposition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  is-prop-Discrete-Premetric : is-prop (Discrete-Premetric l2 A)
  is-prop-Discrete-Premetric =
    is-prop-all-elements-equal all-elements-equal-Discrete-Premetric
```

### Properties of the canonical discrete premetric

#### The canonical discrete premetric on a type is symmetric

```agda
module _
  {l : Level} (A : UU l)
  where

  is-symmetric-discrete-Premetric :
    is-symmetric-Premetric (premetric-discrete-Premetric A)
  is-symmetric-discrete-Premetric d x y =
    rec-trunc-Prop
      ( trunc-Prop (y ＝ x))
      ( unit-trunc-Prop ∘ inv)
```

#### The canonical discrete premetric on a type is triangular

```agda
module _
  {l : Level} (A : UU l)
  where

  is-triangular-discrete-Premetric :
    is-triangular-Premetric (premetric-discrete-Premetric A)
  is-triangular-discrete-Premetric x y z d₁ d₂ H =
    rec-trunc-Prop
      ( trunc-Prop (x ＝ z))
      ( λ (i : x ＝ y) →
        rec-trunc-Prop
          ( trunc-Prop (x ＝ z))
          ( λ (j : y ＝ z) → unit-trunc-Prop (i ∙ j))
          ( H))
```

#### Neighbors in the canonical discrete premetric are indistinguishable

```agda
module _
  {l : Level} (A : UU l) (d : ℚ⁺) (x y : A)
  where

  is-indistinguishable-is-in-neighborhood-discrete-Premetric :
    neighborhood-Premetric (premetric-discrete-Premetric A) d x y →
    is-indistinguishable-Premetric (premetric-discrete-Premetric A) x y
  is-indistinguishable-is-in-neighborhood-discrete-Premetric H d = H
```

#### The canonical discrete premetric on a type is local if and only if this type is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-is-local-discrete-Premetric :
    is-local-Premetric (premetric-discrete-Premetric A) → is-set A
  is-set-is-local-discrete-Premetric =
    ( is-set-has-extensional-Premetric (premetric-discrete-Premetric A)) ∘
    ( pair (is-reflexive-premetric-Discrete-Premetric (discrete-Premetric A)))

  is-local-is-set-discrete-Premetric :
    is-set A → is-local-Premetric (premetric-discrete-Premetric A)
  is-local-is-set-discrete-Premetric H =
    is-local-is-tight-Premetric
      ( premetric-discrete-Premetric A)
      ( λ x y I → rec-trunc-Prop (Id-Prop (A , H) x y) id (I one-ℚ⁺))
```
