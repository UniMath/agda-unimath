# Strict complemented inequality on cardinals

```agda
module set-theory.strict-complemented-inequality-cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-embeddings
open import foundation.nonsurjective-maps
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinalities
open import set-theory.complemented-inequality-cardinalities
open import set-theory.inequality-cardinalities
open import set-theory.strict-complemented-boundedness-cardinalities
```

</details>

## Idea

We may say a [cardinal of sets](set-theory.cardinalities.md) `X` is
{{#concept "less than" Agda=le-complemented-Cardinal}} a cardinal `Y` if any
[set](foundation-core.sets.md) in the isomorphism class represented by `X`
embeds as a complemented subset into any set in the isomorphism class
represented by `Y`, and every decidable embedding `X ↪ Y` is
[nonsurjective](foundation.nonsurjective-maps.md) in the sense that there is an
element in `Y` they do not hit. This is a positive way of saying that `X` and
`Y` are different. This defines a
{{#concept "strict ordering" Disambiguation="on cardinalities of sets"}} on
cardinalities of sets.

## Definition

### The underlying strict complemented inequality of cardinalitiess

```agda
module _
  {l1 l2 : Level}
  where

  le-complemented-prop-cardinality' : Set l1 → Set l2 → Prop (l1 ⊔ l2)
  le-complemented-prop-cardinality' X Y =
    ( leq-complemented-prop-cardinality X Y) ∧
    ( strictly-complemented-bounded-prop-cardinality X Y)

  le-complemented-cardinality' : Set l1 → Set l2 → UU (l1 ⊔ l2)
  le-complemented-cardinality' X Y =
    type-Prop (le-complemented-prop-cardinality' X Y)

  is-prop-le-complemented-cardinality' :
    (X : Set l1) (Y : Set l2) → is-prop (le-complemented-cardinality' X Y)
  is-prop-le-complemented-cardinality' X Y =
    is-prop-type-Prop (le-complemented-prop-cardinality' X Y)
```

### Strict complemented inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-complemented-prop-Cardinal : Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-complemented-prop-Cardinal X Y =
    ( leq-complemented-prop-Cardinal X Y) ∧
    ( strictly-complemented-bounded-prop-Cardinal X Y)

  le-complemented-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  le-complemented-Cardinal X Y = type-Prop (le-complemented-prop-Cardinal X Y)

  is-prop-le-complemented-Cardinal :
    {X : Cardinal l1} {Y : Cardinal l2} → is-prop (le-complemented-Cardinal X Y)
  is-prop-le-complemented-Cardinal {X} {Y} =
    is-prop-type-Prop (le-complemented-prop-Cardinal X Y)
```

### Strict complemented inequality of cardinalitiess

```agda
module _
  {l1 l2 : Level}
  where

  le-complemented-prop-cardinality : Set l1 → Set l2 → Prop (l1 ⊔ l2)
  le-complemented-prop-cardinality X Y =
    ( leq-complemented-prop-cardinality X Y) ∧
    ( strictly-complemented-bounded-prop-cardinality X Y)

  le-complemented-cardinality' : Set l1 → Set l2 → UU (l1 ⊔ l2)
  le-complemented-cardinality' X Y =
    type-Prop (le-complemented-prop-cardinality' X Y)

  is-prop-le-complemented-cardinality' :
    (X : Set l1) (Y : Set l2) → is-prop (le-complemented-cardinality' X Y)
  is-prop-le-complemented-cardinality' X Y =
    is-prop-type-Prop (le-complemented-prop-cardinality' X Y)
```

### Inequality on cardinals is reflexive

```text
refl-le-complemented-cardinality : is-reflexive-Large-Relation Set le-complemented-cardinality
refl-le-complemented-cardinality A = unit-le-complemented-cardinality A A (refl-mere-emb (type-Set A))

refl-le-complemented-Cardinal : is-reflexive-Large-Relation Cardinal le-complemented-Cardinal
refl-le-complemented-Cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (le-complemented-prop-Cardinal X X))
    ( refl-le-complemented-cardinality)
```

### Inequality on cardinals is transitive

```text
module _
  {l1 l2 l3 : Level}
  where

  transitive-le-complemented-cardinality :
    (X : Set l1) (Y : Set l2) (Z : Set l3) →
    le-complemented-cardinality Y Z → le-complemented-cardinality X Y → le-complemented-cardinality X Z
  transitive-le-complemented-cardinality X Y Z Y≤Z X≤Y =
    unit-le-complemented-cardinality X Z
      ( transitive-mere-emb
        ( inv-unit-le-complemented-cardinality Y Z Y≤Z)
        ( inv-unit-le-complemented-cardinality X Y X≤Y))

  transitive-le-complemented-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) (Z : Cardinal l3) →
    le-complemented-Cardinal Y Z → le-complemented-Cardinal X Y → le-complemented-Cardinal X Z
  transitive-le-complemented-Cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        ( le-complemented-Cardinal Y Z → le-complemented-Cardinal X Y → le-complemented-Cardinal X Z) ,
        ( is-set-function-type
          ( is-set-function-type
            ( is-set-is-prop is-prop-le-complemented-Cardinal))))
      ( transitive-le-complemented-cardinality)
```

## Properties

### Assuming excluded middle, then inequality is antisymmetric

Using the previous result and assuming excluded middle, we can conclude
`le-complemented-Cardinal` is a partial order by showing that it is
antisymmetric.

```text
module _
  {l : Level} (lem : LEM l)
  where

  antisymmetric-le-complemented-cardinality :
    (X Y : Set l) →
    le-complemented-cardinality X Y →
    le-complemented-cardinality Y X →
    cardinality X ＝ cardinality Y
  antisymmetric-le-complemented-cardinality X Y X≤Y Y≤X =
    eq-mere-equiv-cardinality X Y
      ( antisymmetric-mere-emb
        ( lem)
        ( inv-unit-le-complemented-cardinality X Y X≤Y)
        ( inv-unit-le-complemented-cardinality Y X Y≤X))

  antisymmetric-le-complemented-Cardinal :
    (X Y : Cardinal l) →
    le-complemented-Cardinal X Y → le-complemented-Cardinal Y X → X ＝ Y
  antisymmetric-le-complemented-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( le-complemented-Cardinal X Y)
            ( function-Prop (le-complemented-Cardinal Y X) (Id-Prop (Cardinal-Set l) X Y))))
      ( antisymmetric-le-complemented-cardinality)
```

## External links

- [Cardinality](https://en.wikipedia.org/wiki/Cardinality) at Wikipedia
- [cardinal number](https://ncatlab.org/nlab/show/cardinal+number) at $n$Lab
