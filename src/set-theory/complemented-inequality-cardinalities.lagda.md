# Complemented inequality on cardinals

```agda
module set-theory.complemented-inequality-cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.mere-decidable-embeddings
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinalities
```

</details>

## Idea

We may say a [cardinal of sets](set-theory.cardinalities.md) `X` is
{{#concept "less than or equal to" Agda=leq-complemented-cardinality}} a
cardinal `Y` if any [set](foundation-core.sets.md) in the isomorphism class
represented by `X` [embeds](foundation-core.embeddings.md) as a
[complemented subtype](foundation.decidable-subtypes.md) into any set in the
isomorphism class represented by `Y`. In other words, if there is a
[decidable embedding](foundation.decidable-embeddings.md) from one to the other.
This defines the
{{#concept "complemented ordering" Disambiguation="on cardinalities of sets"}}
on cardinalities of sets.

Under the assumption of the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md),
this relation is antisymmetric and hence defines a
[partial order](order-theory.posets.md) on cardinalites.

## Definition

### Complemented boundedness of the cardinality of a set

```agda
leq-complemented-prop-cardinal' :
  {l1 l2 : Level} → Set l1 → cardinal l2 → Prop (l1 ⊔ l2)
leq-complemented-prop-cardinal' {l1} {l2} X =
  map-universal-property-trunc-Set
    ( Prop-Set (l1 ⊔ l2))
    ( λ Y' → mere-decidable-emb-Prop (type-Set X) (type-Set Y'))

compute-leq-complemented-prop-cardinal' :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  ( leq-complemented-prop-cardinal' X (cardinality Y)) ＝
  ( mere-decidable-emb-Prop (type-Set X) (type-Set Y))
compute-leq-complemented-prop-cardinal' {l1} {l2} X =
  triangle-universal-property-trunc-Set
    ( Prop-Set (l1 ⊔ l2))
    ( λ Y' → mere-decidable-emb-Prop (type-Set X) (type-Set Y'))
```

### Complemented inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  leq-complemented-prop-cardinal :
    cardinal l1 → cardinal l2 → Prop (l1 ⊔ l2)
  leq-complemented-prop-cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( leq-complemented-prop-cardinal')

  leq-complemented-cardinal :
    cardinal l1 → cardinal l2 → UU (l1 ⊔ l2)
  leq-complemented-cardinal X Y =
    type-Prop (leq-complemented-prop-cardinal X Y)

  is-prop-leq-complemented-cardinal :
    {X : cardinal l1} {Y : cardinal l2} →
    is-prop (leq-complemented-cardinal X Y)
  is-prop-leq-complemented-cardinal {X} {Y} =
    is-prop-type-Prop (leq-complemented-prop-cardinal X Y)
```

### Complemented inequality of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-complemented-prop-cardinality : Prop (l1 ⊔ l2)
  leq-complemented-prop-cardinality =
    leq-complemented-prop-cardinal (cardinality X) (cardinality Y)

  leq-complemented-cardinality : UU (l1 ⊔ l2)
  leq-complemented-cardinality =
    leq-complemented-cardinal (cardinality X) (cardinality Y)

  is-prop-leq-complemented-cardinality :
    is-prop leq-complemented-cardinality
  is-prop-leq-complemented-cardinality =
    is-prop-leq-complemented-cardinal

  compute-leq-complemented-cardinality' :
    leq-complemented-cardinality ＝
    mere-decidable-emb (type-Set X) (type-Set Y)
  compute-leq-complemented-cardinality' =
    ap
      ( type-Prop)
      ( ( htpy-eq
          ( triangle-universal-property-trunc-Set
            ( hom-set-Set (cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
            ( leq-complemented-prop-cardinal') X) (cardinality Y)) ∙
        ( compute-leq-complemented-prop-cardinal' X Y))

  compute-leq-complemented-cardinality :
    leq-complemented-cardinality ≃
    mere-decidable-emb (type-Set X) (type-Set Y)
  compute-leq-complemented-cardinality =
    equiv-eq compute-leq-complemented-cardinality'

  unit-leq-complemented-cardinality :
    mere-decidable-emb (type-Set X) (type-Set Y) →
    leq-complemented-cardinality
  unit-leq-complemented-cardinality =
    map-inv-equiv compute-leq-complemented-cardinality

  inv-unit-leq-complemented-cardinality :
    leq-complemented-cardinality →
    mere-decidable-emb (type-Set X) (type-Set Y)
  inv-unit-leq-complemented-cardinality =
    pr1 compute-leq-complemented-cardinality
```

### Complemented inequality on cardinals is reflexive

```agda
refl-leq-complemented-cardinality :
  is-reflexive-Large-Relation Set leq-complemented-cardinality
refl-leq-complemented-cardinality A =
  unit-leq-complemented-cardinality A A
    ( refl-mere-decidable-emb (type-Set A))

refl-leq-complemented-cardinal :
  is-reflexive-Large-Relation cardinal leq-complemented-cardinal
refl-leq-complemented-cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (leq-complemented-prop-cardinal X X))
    ( refl-leq-complemented-cardinality)
```

### Complemented inequality on cardinals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  where

  transitive-leq-complemented-cardinality :
    (X : Set l1) (Y : Set l2) (Z : Set l3) →
    leq-complemented-cardinality Y Z →
    leq-complemented-cardinality X Y →
    leq-complemented-cardinality X Z
  transitive-leq-complemented-cardinality X Y Z Y≤Z X≤Y =
    unit-leq-complemented-cardinality X Z
      ( transitive-mere-decidable-emb
        ( inv-unit-leq-complemented-cardinality Y Z Y≤Z)
        ( inv-unit-leq-complemented-cardinality X Y X≤Y))

  transitive-leq-complemented-cardinal :
    (X : cardinal l1) (Y : cardinal l2) (Z : cardinal l3) →
    leq-complemented-cardinal Y Z →
    leq-complemented-cardinal X Y →
    leq-complemented-cardinal X Z
  transitive-leq-complemented-cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        ( leq-complemented-cardinal Y Z →
          leq-complemented-cardinal X Y →
          leq-complemented-cardinal X Z) ,
        ( is-set-function-type
          ( is-set-function-type
            ( is-set-is-prop is-prop-leq-complemented-cardinal))))
      ( transitive-leq-complemented-cardinality)
```

## Properties

### Assuming the weak limited principle of omniscience, then complemented inequality is antisymmetric

Using the previous result and assuming the weak limited principle of
omniscience, we can conclude `leq-complemented-cardinal` is a partial order by
showing that it is antisymmetric.

> This remains to be formalized.

```text
module _
  {l : Level} (wlpo : WLPO l)
  where

  antisymmetric-leq-complemented-cardinality :
    (X Y : Set l) →
    leq-complemented-cardinality X Y →
    leq-complemented-cardinality Y X →
    cardinality X ＝ cardinality Y
  antisymmetric-leq-complemented-cardinality X Y X≤Y Y≤X =
    eq-mere-equiv-cardinality X Y
      ( antisymmetric-mere-decidable-emb
        ( wlpo)
        ( inv-unit-leq-complemented-cardinality X Y X≤Y)
        ( inv-unit-leq-complemented-cardinality Y X Y≤X))

  antisymmetric-leq-complemented-cardinal :
    (X Y : cardinal l) →
    leq-complemented-cardinal X Y → leq-complemented-cardinal Y X → X ＝ Y
  antisymmetric-leq-complemented-cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( leq-complemented-cardinal X Y)
            ( function-Prop
              ( leq-complemented-cardinal Y X)
              ( Id-Prop (cardinal-Set l) X Y))))
      ( antisymmetric-leq-complemented-cardinality)
```
