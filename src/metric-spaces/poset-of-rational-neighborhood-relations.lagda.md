# The poset of rational neighborhood relations on a type

```agda
module metric-spaces.poset-of-rational-neighborhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.rational-neighborhood-relations

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
`U` on a type `A` is
{{#concept "finer" Disambiguation="rational neighborhood relation on a type" Agda=leq-Rational-Neighborhood-Relation}}
than another rational neighborhood relation `V` if `(U d)`-neighborhoods are
`(V d)`-neighborhoods for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `d`,
i.e., if any upper bound on the distance between two points in `U` also bounds
their distance in `V`. This defines a [partial order](order-theory.posets.md) on
the type of rational neighborhood relations on `A`.

## Definitions

```agda
module _
  {l1 l2 l2' : Level} {A : UU l1}
  (U : Rational-Neighborhood-Relation l2 A)
  (V : Rational-Neighborhood-Relation l2' A)
  where

  leq-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2 ⊔ l2')
  leq-prop-Rational-Neighborhood-Relation =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → hom-Prop (U d x y) (V d x y))))

  leq-Rational-Neighborhood-Relation : UU (l1 ⊔ l2 ⊔ l2')
  leq-Rational-Neighborhood-Relation =
    type-Prop leq-prop-Rational-Neighborhood-Relation

  is-prop-leq-Rational-Neighborhood-Relation :
    is-prop leq-Rational-Neighborhood-Relation
  is-prop-leq-Rational-Neighborhood-Relation =
    is-prop-type-Prop leq-prop-Rational-Neighborhood-Relation
```

## Properties

### The ordering on rational neighborhood relations is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Rational-Neighborhood-Relation l2 A)
  where

  refl-leq-Rational-Neighborhood-Relation :
    leq-Rational-Neighborhood-Relation U U
  refl-leq-Rational-Neighborhood-Relation d x y H = H

  leq-eq-Rational-Neighborhood-Relation :
    (V : Rational-Neighborhood-Relation l2 A) →
    (U ＝ V) →
    leq-Rational-Neighborhood-Relation U V
  leq-eq-Rational-Neighborhood-Relation .U refl =
    refl-leq-Rational-Neighborhood-Relation
```

### The ordering on rational neighborhood relations is transitive

```agda
module _
  {l lu lv lw : Level} {A : UU l}
  (U : Rational-Neighborhood-Relation lu A)
  (V : Rational-Neighborhood-Relation lv A)
  (W : Rational-Neighborhood-Relation lw A)
  where

  transitive-leq-Rational-Neighborhood-Relation :
    leq-Rational-Neighborhood-Relation V W →
    leq-Rational-Neighborhood-Relation U V →
    leq-Rational-Neighborhood-Relation U W
  transitive-leq-Rational-Neighborhood-Relation H K d x y = H d x y ∘ K d x y
```

### The ordering on rational neighborhood relations is antisymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V : Rational-Neighborhood-Relation l2 A)
  where

  antisymmetric-leq-Rational-Neighborhood-Relation :
    leq-Rational-Neighborhood-Relation U V →
    leq-Rational-Neighborhood-Relation V U →
    U ＝ V
  antisymmetric-leq-Rational-Neighborhood-Relation I J =
    eq-Eq-Rational-Neighborhood-Relation
      ( U)
      ( V)
      ( λ d x y → (I d x y , J d x y))
```

### The poset of rational neighborhood relations on a type

```agda
module _
  {l1 l2 : Level} (A : UU l1)
  where

  preorder-Rational-Neighborhood-Relation : Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 preorder-Rational-Neighborhood-Relation =
    Rational-Neighborhood-Relation l2 A
  pr2 preorder-Rational-Neighborhood-Relation =
    leq-prop-Rational-Neighborhood-Relation ,
    refl-leq-Rational-Neighborhood-Relation ,
    transitive-leq-Rational-Neighborhood-Relation

  poset-Rational-Neighborhood-Relation : Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  poset-Rational-Neighborhood-Relation =
    preorder-Rational-Neighborhood-Relation ,
    antisymmetric-leq-Rational-Neighborhood-Relation
```
