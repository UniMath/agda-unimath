# Transitive Closures

```agda
module foundation.transitive-closures-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

### Transitive closures of binary relations valued in types

The {{#concept "transitive closure" Agda=transitive-closure-Relation}} of a
[binary relation](foundation.binary-relations.md) `R : A → A → Type` is a
transitive binary relation `R' : A → A → Type` equipped with a family of maps

```text
  (x y : A) → R x y → R' x y,
```

satisfying the universal property that for any transitive binary relation
`S : A → A → Type` the evaluation map

```text
  hom-transitive-relation R' S → (x y : A) → R x y → S x y
```

is an [equivalence](foundation-core.equivalences.md). Here, the type
`hom-transitive-relation R' S` is the type of families of maps

```text
  (x y : A) → R' x y → S x y
```

that preserve the composition operation.

### Transitive closures of binary relations valued in propositions

The transitive closure of a binary relation `R : A → A → Prop` valued in
[propositions](foundation-core.propositions.md) is the least transitive relation
containing `R`. In other words, it is a transitive relation `R' : A → A → Prop`
such that for any transitive relation `S : A → A → Prop` the map

```text
  ((x y : A) → R' x y → S x y) → ((x y : A) → R x y → S x y)
```

is an equivalence. Since the relations here are all valued in propositions, and
hence proof irrelevant, we do not need to require that the morphisms from `R'`
to `S` preserve composition.

## Definitions

### The transitive closure of a binary relation valued in types

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  data transitive-closure-Relation (R : Relation l2 A) : Relation (l1 ⊔ l2) A
    where
    base-transitive-closure-Relation : {x y : A} → R x y → transitive-closure-Relation R x y
    step-transitive-closure-Relation :
      {x y z : A} → R x y → transitive-closure-Relation R y z → transitive-closure-Relation R x z

  is-transitive-transitive-closure-Relation :
    (R : Relation l2 A) → is-transitive (transitive-closure-Relation R)
  is-transitive-transitive-closure-Relation
    R x y z c-yz (base-transitive-closure-Relation r-xy) =
      step-transitive-closure-Relation r-xy c-yz
  is-transitive-transitive-closure-Relation
    R x y z c-yz (step-transitive-closure-Relation {y = u} r-xu c-uy) =
      step-transitive-closure-Relation r-xu
        ( is-transitive-transitive-closure-Relation R u y z c-yz c-uy)
```

### Transitive closure of a relation valued in propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  transitive-closure-Relation-Prop :
    (R : Relation-Prop l2 A) → Relation-Prop (l1 ⊔ l2) A
  transitive-closure-Relation-Prop R x y =
    trunc-Prop (transitive-closure-Relation (type-Relation-Prop R) x y)

  is-transitive-transitive-closure-Relation-Prop :
    (R : Relation-Prop l2 A) →
    is-transitive-Relation-Prop (transitive-closure-Relation-Prop R)
  is-transitive-transitive-closure-Relation-Prop R x y z c-yz c-xy =
    apply-twice-universal-property-trunc-Prop
      ( c-yz)
      ( c-xy)
      ( transitive-closure-Relation-Prop R x z)
      ( λ r-yz r-xy →
        unit-trunc-Prop
          ( is-transitive-transitive-closure-Relation
            ( type-Relation-Prop R)
            ( x)
            ( y)
            ( z)
            ( r-yz)
            ( r-xy)))
```

## Properties

### The transitive closure of a reflexive relation valued in types is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-reflexive-transitive-closure-is-reflexive-Relation :
    (R : Relation l2 A) →
    is-reflexive R →
    is-reflexive (transitive-closure-Relation R)
  is-reflexive-transitive-closure-is-reflexive-Relation R is-refl x =
    base-transitive-closure-Relation (is-refl x)
```

### The transitive closure of a symmetric relation valued in types is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-symmetric-transitive-closure-is-symmetric-Relation :
    (R : Relation l2 A) →
    is-symmetric R →
    is-symmetric (transitive-closure-Relation R)
  is-symmetric-transitive-closure-is-symmetric-Relation R is-sym x y
    (base-transitive-closure-Relation r) =
      base-transitive-closure-Relation (is-sym x y r)
  is-symmetric-transitive-closure-is-symmetric-Relation
    R is-sym x y (step-transitive-closure-Relation {y = u} r-xu c-uy) =
      is-transitive-transitive-closure-Relation R y u x
        ( base-transitive-closure-Relation (is-sym x u r-xu))
        ( is-symmetric-transitive-closure-is-symmetric-Relation R is-sym u y c-uy)
```

### The transitive closure of a reflexive relation valued in propositions is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-reflexive-transitive-closure-is-reflexive-Relation-Prop :
    (R : Relation-Prop l2 A) →
    is-reflexive-Relation-Prop R →
    is-reflexive-Relation-Prop (transitive-closure-Relation-Prop R)
  is-reflexive-transitive-closure-is-reflexive-Relation-Prop R is-refl x =
    unit-trunc-Prop
      ( is-reflexive-transitive-closure-is-reflexive-Relation
        ( type-Relation-Prop R)
        ( is-refl)
        ( x))
```

### The transitive closure of a symmetric relation valued in propositions is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-symmetric-transitive-closure-is-symmetric-Relation-Prop :
    (R : Relation-Prop l2 A) →
    is-symmetric-Relation-Prop R →
    is-symmetric-Relation-Prop (transitive-closure-Relation-Prop R)
  is-symmetric-transitive-closure-is-symmetric-Relation-Prop R is-sym x y =
    map-universal-property-trunc-Prop
      ( transitive-closure-Relation-Prop R y x)
      ( λ r-xy →
        unit-trunc-Prop
          ( is-symmetric-transitive-closure-is-symmetric-Relation
            ( type-Relation-Prop R)
            ( is-sym)
            ( x)
            ( y)
            ( r-xy)))
```
