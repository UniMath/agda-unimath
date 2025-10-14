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

We say a [cardinality of sets](set-theory.cardinalities.md) `X` is
{{#concept "less than or equal to" Agda=leq-cardinal}} a cardinality `Y` if any
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
leq-prop-cardinal' :
  {l1 l2 : Level} → Set l1 → cardinal l2 → Prop (l1 ⊔ l2)
leq-prop-cardinal' {l1} {l2} X =
  map-universal-property-trunc-Set
    ( Prop-Set (l1 ⊔ l2))
    ( λ Y' → mere-emb-Prop (type-Set X) (type-Set Y'))

compute-leq-prop-cardinal' :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  ( leq-prop-cardinal' X (cardinality Y)) ＝
  ( mere-emb-Prop (type-Set X) (type-Set Y))
compute-leq-prop-cardinal' {l1} {l2} X =
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

  compute-leq-cardinality' :
    leq-cardinality ＝ mere-emb (type-Set X) (type-Set Y)
  compute-leq-cardinality' =
    ap
      ( type-Prop)
      ( ( htpy-eq
          ( triangle-universal-property-trunc-Set
            ( hom-set-Set (cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
            ( leq-prop-cardinal') X) (cardinality Y)) ∙
        ( compute-leq-prop-cardinal' X Y))

  compute-leq-cardinality :
    leq-cardinality ≃ mere-emb (type-Set X) (type-Set Y)
  compute-leq-cardinality = equiv-eq compute-leq-cardinality'

  unit-leq-cardinality :
    mere-emb (type-Set X) (type-Set Y) → leq-cardinality
  unit-leq-cardinality = map-inv-equiv compute-leq-cardinality

  inv-unit-leq-cardinality :
    leq-cardinality → mere-emb (type-Set X) (type-Set Y)
  inv-unit-leq-cardinality = pr1 compute-leq-cardinality
```

### Inequality on cardinals is reflexive

```agda
refl-leq-cardinal : is-reflexive-Large-Relation cardinal leq-cardinal
refl-leq-cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (leq-prop-cardinal X X))
    ( λ A → unit-leq-cardinality A A (refl-mere-emb (type-Set A)))
```

### Inequality on cardinals is transitive

```agda
transitive-leq-cardinal :
  {l1 l2 l3 : Level}
  (X : cardinal l1)
  (Y : cardinal l2)
  (Z : cardinal l3) →
  leq-cardinal X Y →
  leq-cardinal Y Z →
  leq-cardinal X Z
transitive-leq-cardinal X Y Z =
  apply-dependent-universal-property-trunc-Set'
    ( λ u →
      set-Prop
        ( function-Prop
          ( leq-cardinal u Y)
          ( function-Prop (leq-cardinal Y Z)
            ( leq-prop-cardinal u Z))))
    ( λ a →
      apply-dependent-universal-property-trunc-Set'
        ( λ v →
          set-Prop
            (function-Prop
              (leq-cardinal (cardinality a) v)
              (function-Prop (leq-cardinal v Z)
                (leq-prop-cardinal (cardinality a) Z))))
        ( λ b →
          apply-dependent-universal-property-trunc-Set'
          ( λ w →
            set-Prop
              (function-Prop
                (leq-cardinal (cardinality a) (cardinality b))
                (function-Prop (leq-cardinal (cardinality b) w)
                  (leq-prop-cardinal (cardinality a) w))))
          ( λ c a<b b<c →
            unit-leq-cardinality
              ( a)
              ( c)
              ( transitive-mere-emb
                ( inv-unit-leq-cardinality b c b<c)
                ( inv-unit-leq-cardinality a b a<b)))
          ( Z))
        ( Y))
    ( X)
```

## Properties

### Assuming excluded middle, then inequality is antisymmetric

Using the previous result and assuming excluded middle, we can conclude
`leq-cardinal` is a partial order by showing that it is antisymmetric.

```agda
antisymmetric-leq-cardinal :
  {l : Level} → LEM l → (X Y : cardinal l) →
  leq-cardinal X Y → leq-cardinal Y X → X ＝ Y
antisymmetric-leq-cardinal {l} lem X Y =
  apply-dependent-universal-property-trunc-Set'
  ( λ u →
    set-Prop
      ( function-Prop
        ( leq-cardinal u Y)
        ( function-Prop
          ( leq-cardinal Y u)
          ( Id-Prop (cardinal-Set l) u Y))))
  ( λ a →
    apply-dependent-universal-property-trunc-Set'
      ( λ v →
        set-Prop
          ( function-Prop
            ( leq-cardinal (cardinality a) v)
            ( function-Prop
              ( leq-cardinal v (cardinality a))
              ( Id-Prop (cardinal-Set l) (cardinality a) v))))
      ( λ b a<b b<a →
        eq-mere-equiv-cardinality a b
          ( antisymmetric-mere-emb lem
            ( inv-unit-leq-cardinality _ _ a<b)
            ( inv-unit-leq-cardinality _ _ b<a)))
      ( Y))
  ( X)
```

## External links

- [Cardinality](https://en.wikipedia.org/wiki/Cardinality) at Wikipedia
- [cardinal number](https://ncatlab.org/nlab/show/cardinal+number) at $n$Lab
