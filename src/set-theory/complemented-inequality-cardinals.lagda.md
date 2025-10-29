# Complemented inequality on cardinals

```agda
module set-theory.complemented-inequality-cardinals where
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
open import foundation.weak-limited-principle-of-omniscience

open import order-theory.large-posets
open import order-theory.large-preorders

open import set-theory.cardinals
open import set-theory.equality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is
{{#concept "less than or equal to" Agda=leq-complemented-Cardinal}} a cardinal
`Y` if any [set](foundation-core.sets.md) in the isomorphism class represented
by `X` [embeds](foundation-core.embeddings.md) as a
[complemented subtype](foundation.decidable-subtypes.md) into any set in the
isomorphism class represented by `Y`. In other words, if there is a
[decidable embedding](foundation.decidable-embeddings.md) from the first to the
second. This defines the
{{#concept "complemented ordering" Disambiguation="on cardinalities of sets"}}
on cardinalities of sets.

Under the assumption of the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md),
this relation is antisymmetric and hence defines a
[partial order](order-theory.posets.md) on cardinals.

## Definition

### Complemented boundedness of the cardinality of a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  leq-complemented-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  leq-complemented-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-decidable-emb-Prop (type-Set X) (type-Set Y'))

  compute-leq-complemented-prop-Cardinal' :
    (Y : Set l2) →
    leq-complemented-prop-Cardinal' (cardinality Y) ＝
    mere-decidable-emb-Prop (type-Set X) (type-Set Y)
  compute-leq-complemented-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-decidable-emb-Prop (type-Set X) (type-Set Y'))
```

### Complemented inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  leq-complemented-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  leq-complemented-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( leq-complemented-prop-Cardinal')

  leq-complemented-Cardinal :
    Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  leq-complemented-Cardinal X Y =
    type-Prop (leq-complemented-prop-Cardinal X Y)

  is-prop-leq-complemented-Cardinal :
    {X : Cardinal l1} {Y : Cardinal l2} →
    is-prop (leq-complemented-Cardinal X Y)
  is-prop-leq-complemented-Cardinal {X} {Y} =
    is-prop-type-Prop (leq-complemented-prop-Cardinal X Y)
```

### Complemented inequality of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-complemented-prop-cardinality : Prop (l1 ⊔ l2)
  leq-complemented-prop-cardinality =
    leq-complemented-prop-Cardinal (cardinality X) (cardinality Y)

  leq-complemented-cardinality : UU (l1 ⊔ l2)
  leq-complemented-cardinality =
    leq-complemented-Cardinal (cardinality X) (cardinality Y)

  is-prop-leq-complemented-cardinality :
    is-prop leq-complemented-cardinality
  is-prop-leq-complemented-cardinality =
    is-prop-leq-complemented-Cardinal

  compute-leq-complemented-prop-cardinality' :
    leq-complemented-prop-cardinality ＝
    mere-decidable-emb-Prop (type-Set X) (type-Set Y)
  compute-leq-complemented-prop-cardinality' =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( leq-complemented-prop-Cardinal') X) (cardinality Y)) ∙
    ( compute-leq-complemented-prop-Cardinal' X Y)

  compute-leq-complemented-cardinality' :
    leq-complemented-cardinality ＝
    mere-decidable-emb (type-Set X) (type-Set Y)
  compute-leq-complemented-cardinality' =
    ap type-Prop compute-leq-complemented-prop-cardinality'

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

refl-leq-complemented-Cardinal :
  is-reflexive-Large-Relation Cardinal leq-complemented-Cardinal
refl-leq-complemented-Cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (leq-complemented-prop-Cardinal X X))
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

  transitive-leq-complemented-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) (Z : Cardinal l3) →
    leq-complemented-Cardinal Y Z →
    leq-complemented-Cardinal X Y →
    leq-complemented-Cardinal X Z
  transitive-leq-complemented-Cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        ( leq-complemented-Cardinal Y Z →
          leq-complemented-Cardinal X Y →
          leq-complemented-Cardinal X Z) ,
        ( is-set-function-type
          ( is-set-function-type
            ( is-set-is-prop is-prop-leq-complemented-Cardinal))))
      ( transitive-leq-complemented-cardinality)
```

## Properties

### Assuming the weak limited principle of omniscience, then complemented inequality is antisymmetric

Using the previous result and assuming the weak limited principle of
omniscience, we can conclude `leq-complemented-Cardinal` is a partial order by
showing that it is antisymmetric.

```agda
module _
  {l : Level} (wlpo : level-WLPO l)
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

  antisymmetric-leq-complemented-Cardinal :
    (X Y : Cardinal l) →
    leq-complemented-Cardinal X Y → leq-complemented-Cardinal Y X → X ＝ Y
  antisymmetric-leq-complemented-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( leq-complemented-Cardinal X Y)
            ( function-Prop
              ( leq-complemented-Cardinal Y X)
              ( Id-Prop (Cardinal-Set l) X Y))))
      ( antisymmetric-leq-complemented-cardinality)
```

### The large poset of cardinals under complemented inequality

```agda
large-preorder-complemented-Cardinal : Large-Preorder lsuc (_⊔_)
large-preorder-complemented-Cardinal =
  λ where
  .type-Large-Preorder → Cardinal
  .leq-prop-Large-Preorder → leq-complemented-prop-Cardinal
  .refl-leq-Large-Preorder → refl-leq-complemented-Cardinal
  .transitive-leq-Large-Preorder → transitive-leq-complemented-Cardinal

large-poset-complemented-Cardinal : WLPO → Large-Poset lsuc (_⊔_)
large-poset-complemented-Cardinal wlpo =
  λ where
  .large-preorder-Large-Poset → large-preorder-complemented-Cardinal
  .antisymmetric-leq-Large-Poset → antisymmetric-leq-complemented-Cardinal wlpo
```
