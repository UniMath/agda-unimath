# Inequality on cardinals

```agda
module set-theory.inequality-cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-embeddings
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

We say a [cardinal of sets](set-theory.cardinalities.md) `X` is
{{#concept "less than or equal to" Agda=leq-cardinal}} a cardinal `Y` if any
[set](foundation-core.sets.md) in the isomorphism class represented by `X`
embeds into any set in the isomorphism class represented by `Y`. This defines
the {{#concept "standard ordering" Disambiguation="on cardinalities of sets"}}
on cardinalities of sets.

Under the assumption of the
[law of excluded middle](foundation.law-of-excluded-middle.md), this relation is
antisymmetric and hence defines a [partial order](order-theory.posets.md) on
cardinalites.

## Definition

### Boundedness of the cardinality of a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  leq-prop-cardinal' : cardinal l2 → Prop (l1 ⊔ l2)
  leq-prop-cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-emb-Prop (type-Set X) (type-Set Y'))

  compute-leq-prop-cardinal' :
    (Y : Set l2) →
    leq-prop-cardinal' (cardinality Y) ＝
    mere-emb-Prop (type-Set X) (type-Set Y)
  compute-leq-prop-cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-emb-Prop (type-Set X) (type-Set Y'))
```

### Inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  leq-prop-cardinal : cardinal l1 → cardinal l2 → Prop (l1 ⊔ l2)
  leq-prop-cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( leq-prop-cardinal')

  leq-cardinal : cardinal l1 → cardinal l2 → UU (l1 ⊔ l2)
  leq-cardinal X Y = type-Prop (leq-prop-cardinal X Y)

  is-prop-leq-cardinal :
    {X : cardinal l1} {Y : cardinal l2} → is-prop (leq-cardinal X Y)
  is-prop-leq-cardinal {X} {Y} = is-prop-type-Prop (leq-prop-cardinal X Y)
```

### Inequality of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-prop-cardinality : Prop (l1 ⊔ l2)
  leq-prop-cardinality = leq-prop-cardinal (cardinality X) (cardinality Y)

  leq-cardinality : UU (l1 ⊔ l2)
  leq-cardinality = leq-cardinal (cardinality X) (cardinality Y)

  is-prop-leq-cardinality : is-prop leq-cardinality
  is-prop-leq-cardinality = is-prop-leq-cardinal

  eq-compute-leq-prop-cardinality :
    leq-prop-cardinality ＝ mere-emb-Prop (type-Set X) (type-Set Y)
  eq-compute-leq-prop-cardinality =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( leq-prop-cardinal') X) (cardinality Y)) ∙
    ( compute-leq-prop-cardinal' X Y)

  eq-compute-leq-cardinality :
    leq-cardinality ＝ mere-emb (type-Set X) (type-Set Y)
  eq-compute-leq-cardinality =
    ap type-Prop eq-compute-leq-prop-cardinality

  compute-leq-cardinality :
    leq-cardinality ≃ mere-emb (type-Set X) (type-Set Y)
  compute-leq-cardinality = equiv-eq eq-compute-leq-cardinality

  unit-leq-cardinality :
    mere-emb (type-Set X) (type-Set Y) → leq-cardinality
  unit-leq-cardinality = map-inv-equiv compute-leq-cardinality

  inv-unit-leq-cardinality :
    leq-cardinality → mere-emb (type-Set X) (type-Set Y)
  inv-unit-leq-cardinality = pr1 compute-leq-cardinality
```

### Inequality on cardinals is reflexive

```agda
refl-leq-cardinality : is-reflexive-Large-Relation Set leq-cardinality
refl-leq-cardinality A = unit-leq-cardinality A A (refl-mere-emb (type-Set A))

refl-leq-cardinal : is-reflexive-Large-Relation cardinal leq-cardinal
refl-leq-cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (leq-prop-cardinal X X))
    ( refl-leq-cardinality)
```

### Inequality on cardinals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  where

  transitive-leq-cardinality :
    (X : Set l1) (Y : Set l2) (Z : Set l3) →
    leq-cardinality Y Z → leq-cardinality X Y → leq-cardinality X Z
  transitive-leq-cardinality X Y Z Y≤Z X≤Y =
    unit-leq-cardinality X Z
      ( transitive-mere-emb
        ( inv-unit-leq-cardinality Y Z Y≤Z)
        ( inv-unit-leq-cardinality X Y X≤Y))

  transitive-leq-cardinal :
    (X : cardinal l1) (Y : cardinal l2) (Z : cardinal l3) →
    leq-cardinal Y Z → leq-cardinal X Y → leq-cardinal X Z
  transitive-leq-cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        ( leq-cardinal Y Z → leq-cardinal X Y → leq-cardinal X Z) ,
        ( is-set-function-type
          ( is-set-function-type
            ( is-set-is-prop is-prop-leq-cardinal))))
      ( transitive-leq-cardinality)
```

## Properties

### Assuming excluded middle, then inequality is antisymmetric

Using the previous result and assuming excluded middle, we can conclude
`leq-cardinal` is a partial order by showing that it is antisymmetric.

```agda
module _
  {l : Level} (lem : LEM l)
  where

  antisymmetric-leq-cardinality :
    (X Y : Set l) →
    leq-cardinality X Y →
    leq-cardinality Y X →
    cardinality X ＝ cardinality Y
  antisymmetric-leq-cardinality X Y X≤Y Y≤X =
    eq-mere-equiv-cardinality X Y
      ( antisymmetric-mere-emb
        ( lem)
        ( inv-unit-leq-cardinality X Y X≤Y)
        ( inv-unit-leq-cardinality Y X Y≤X))

  antisymmetric-leq-cardinal :
    (X Y : cardinal l) →
    leq-cardinal X Y → leq-cardinal Y X → X ＝ Y
  antisymmetric-leq-cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( leq-cardinal X Y)
            ( function-Prop (leq-cardinal Y X) (Id-Prop (cardinal-Set l) X Y))))
      ( antisymmetric-leq-cardinality)
```

## External links

- [Cardinality](https://en.wikipedia.org/wiki/Cardinality) at Wikipedia
- [cardinal number](https://ncatlab.org/nlab/show/cardinal+number) at $n$Lab
