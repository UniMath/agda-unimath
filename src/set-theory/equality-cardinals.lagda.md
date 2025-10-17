# Equality of cardinals

```agda
module set-theory.equality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.mere-equivalences
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

Two [cardinals of sets](set-theory.cardinalities.md) `X` and `Y` are
{{#concept "similar" Disambiguation="cardinals" Agda=sim-Cardinal}} if there
[merely](foundation.inhabited-types.md) is an
[equivalence](foundation-core.equivalences.md) between any two representing two
types. This characterizes [equality](foundation-core.identity-types.md) of
cardinals.

## Definition

### The underlying similarity of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  sim-prop-cardinality' : Prop (l1 ⊔ l2)
  sim-prop-cardinality' = mere-equiv-Prop (type-Set X) (type-Set Y)

  sim-cardinality' : UU (l1 ⊔ l2)
  sim-cardinality' = mere-equiv (type-Set X) (type-Set Y)

  is-prop-sim-sim-cardinality' : is-prop sim-cardinality'
  is-prop-sim-sim-cardinality' = is-prop-mere-equiv (type-Set X) (type-Set Y)

refl-sim-cardinality' : {l : Level} (X : Set l) → sim-cardinality' X X
refl-sim-cardinality' X = refl-mere-equiv (type-Set X)

transitive-sim-cardinality' :
  {l1 l2 l3 : Level} (X : Set l1) (Y : Set l2) (Z : Set l3) →
  sim-cardinality' Y Z → sim-cardinality' X Y → sim-cardinality' X Z
transitive-sim-cardinality' X Y Z =
  transitive-mere-equiv (type-Set X) (type-Set Y) (type-Set Z)

symmetric-sim-cardinality' :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  sim-cardinality' X Y → sim-cardinality' Y X
symmetric-sim-cardinality' X Y =
  symmetric-mere-equiv (type-Set X) (type-Set Y)
```

### Similarity of cardinalities with a cardinal

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  sim-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  sim-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( sim-prop-cardinality' X)

  sim-Cardinal' : Cardinal l2 → UU (l1 ⊔ l2)
  sim-Cardinal' Y = type-Prop (sim-prop-Cardinal' Y)

  is-prop-sim-sim-Cardinal' : (Y : Cardinal l2) → is-prop (sim-Cardinal' Y)
  is-prop-sim-sim-Cardinal' Y = is-prop-type-Prop (sim-prop-Cardinal' Y)

  eq-compute-sim-prop-Cardinal' :
    (Y : Set l2) →
    sim-prop-Cardinal' (cardinality Y) ＝ sim-prop-cardinality' X Y
  eq-compute-sim-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( sim-prop-cardinality' X)

  eq-compute-sim-Cardinal' :
    (Y : Set l2) →
    sim-Cardinal' (cardinality Y) ＝ sim-cardinality' X Y
  eq-compute-sim-Cardinal' Y =
    ap type-Prop (eq-compute-sim-prop-Cardinal' Y)
```

### Similarity of cardinals

```agda
module _
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2)
  where

  sim-prop-Cardinal : Prop (l1 ⊔ l2)
  sim-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( sim-prop-Cardinal')
      ( X)
      ( Y)

  sim-Cardinal : UU (l1 ⊔ l2)
  sim-Cardinal = type-Prop sim-prop-Cardinal

  is-prop-sim-sim-Cardinal : is-prop sim-Cardinal
  is-prop-sim-sim-Cardinal = is-prop-type-Prop sim-prop-Cardinal

  sim-set-Cardinal : Set (l1 ⊔ l2)
  sim-set-Cardinal = set-Prop sim-prop-Cardinal
```

### Similarity of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  sim-prop-cardinality : Prop (l1 ⊔ l2)
  sim-prop-cardinality = sim-prop-Cardinal (cardinality X) (cardinality Y)

  sim-cardinality : UU (l1 ⊔ l2)
  sim-cardinality = type-Prop sim-prop-cardinality

  is-prop-sim-sim-cardinality : is-prop sim-cardinality
  is-prop-sim-sim-cardinality = is-prop-type-Prop sim-prop-cardinality

  eq-compute-sim-prop-cardinality :
    sim-prop-cardinality ＝ mere-equiv-Prop (type-Set X) (type-Set Y)
  eq-compute-sim-prop-cardinality =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( sim-prop-Cardinal')
        ( X))
      ( cardinality Y)) ∙
    ( eq-compute-sim-prop-Cardinal' X Y)

  eq-compute-sim-cardinality :
    sim-cardinality ＝ mere-equiv (type-Set X) (type-Set Y)
  eq-compute-sim-cardinality =
    ap type-Prop eq-compute-sim-prop-cardinality

  compute-sim-cardinality :
    sim-cardinality ≃ mere-equiv (type-Set X) (type-Set Y)
  compute-sim-cardinality = equiv-eq eq-compute-sim-cardinality

  unit-sim-cardinality :
    mere-equiv (type-Set X) (type-Set Y) → sim-cardinality
  unit-sim-cardinality = map-inv-equiv compute-sim-cardinality

  inv-unit-sim-cardinality :
    sim-cardinality → mere-equiv (type-Set X) (type-Set Y)
  inv-unit-sim-cardinality = pr1 compute-sim-cardinality
```

## Properties

### Equality of cardinalities is equivalent to mere equivalence

```agda
is-effective-cardinality :
  {l : Level} (X Y : Set l) →
  (cardinality X ＝ cardinality Y) ≃ mere-equiv (type-Set X) (type-Set Y)
is-effective-cardinality X Y =
  ( equiv-trunc-Prop (extensionality-Set X Y)) ∘e
  ( is-effective-unit-trunc-Set (Set _) X Y)

eq-mere-equiv-cardinality :
  {l : Level} (X Y : Set l) →
  mere-equiv (type-Set X) (type-Set Y) → cardinality X ＝ cardinality Y
eq-mere-equiv-cardinality X Y = map-inv-equiv (is-effective-cardinality X Y)
```

### Similarity of cardinals is reflexive

```agda
refl-sim-cardinality : {l : Level} (X : Set l) → sim-cardinality X X
refl-sim-cardinality X = unit-sim-cardinality X X (refl-mere-equiv (type-Set X))

refl-sim-Cardinal : {l : Level} (X : Cardinal l) → sim-Cardinal X X
refl-sim-Cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → sim-set-Cardinal X X)
    ( refl-sim-cardinality)
```

### Similarity of cardinals is symmetric

```agda
symmetric-sim-cardinality :
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2) →
  sim-cardinality X Y → sim-cardinality Y X
symmetric-sim-cardinality X Y p =
  unit-sim-cardinality Y X
    ( symmetric-sim-cardinality' X Y (inv-unit-sim-cardinality X Y p))

abstract
  symmetric-sim-Cardinal :
    {l1 l2 : Level}
    (X : Cardinal l1) (Y : Cardinal l2) →
    sim-Cardinal X Y → sim-Cardinal Y X
  symmetric-sim-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y → hom-set-Set (sim-set-Cardinal X Y) (sim-set-Cardinal Y X))
      ( symmetric-sim-cardinality)
```

### Similarity of cardinals is transitive

```agda
transitive-sim-cardinality :
  {l1 l2 l3 : Level}
  (X : Set l1) (Y : Set l2) (Z : Set l3) →
  sim-cardinality Y Z → sim-cardinality X Y → sim-cardinality X Z
transitive-sim-cardinality X Y Z p q =
  unit-sim-cardinality X Z
    ( transitive-sim-cardinality' X Y Z
      ( inv-unit-sim-cardinality Y Z p)
      ( inv-unit-sim-cardinality X Y q))

abstract
  transitive-sim-Cardinal :
    {l1 l2 l3 : Level}
    (X : Cardinal l1) (Y : Cardinal l2) (Z : Cardinal l3) →
    sim-Cardinal Y Z → sim-Cardinal X Y → sim-Cardinal X Z
  transitive-sim-Cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        hom-set-Set
          ( sim-set-Cardinal Y Z)
          ( hom-set-Set (sim-set-Cardinal X Y) (sim-set-Cardinal X Z)))
      ( transitive-sim-cardinality)
```

### Similarity of cardinals is extensional

```agda
module _
  {l : Level}
  where

  sim-eq-Cardinal :
      (X Y : Cardinal l) → X ＝ Y → sim-Cardinal X Y
  sim-eq-Cardinal X .X refl = refl-sim-Cardinal X

  sim-eq-cardinality :
      (X Y : Set l) → cardinality X ＝ cardinality Y → sim-cardinality X Y
  sim-eq-cardinality X Y = sim-eq-Cardinal (cardinality X) (cardinality Y)

  eq-sim-cardinality :
    (X Y : Set l) → sim-cardinality X Y → cardinality X ＝ cardinality Y
  eq-sim-cardinality X Y p =
    eq-mere-equiv-cardinality X Y (inv-unit-sim-cardinality X Y p)

  abstract
    eq-sim-Cardinal :
      (X Y : Cardinal l) → sim-Cardinal X Y → X ＝ Y
    eq-sim-Cardinal =
      apply-twice-dependent-universal-property-trunc-Set'
        ( λ X Y →
          hom-set-Set
            ( sim-set-Cardinal X Y)
            ( set-Prop (Id-Prop (Cardinal-Set l) X Y)))
        ( eq-sim-cardinality)

  abstract
    antisymmetric-sim-Cardinal :
      (X Y : Cardinal l) → sim-Cardinal X Y → sim-Cardinal Y X → X ＝ Y
    antisymmetric-sim-Cardinal X Y p _ = eq-sim-Cardinal X Y p
```

### Similarity of cardinals is a large similarity relation

```agda
large-equivalence-relation-Cardinal : Large-Equivalence-Relation (_⊔_) Cardinal
large-equivalence-relation-Cardinal =
  λ where
    .sim-prop-Large-Equivalence-Relation → sim-prop-Cardinal
    .refl-sim-Large-Equivalence-Relation → refl-sim-Cardinal
    .symmetric-sim-Large-Equivalence-Relation → symmetric-sim-Cardinal
    .transitive-sim-Large-Equivalence-Relation → transitive-sim-Cardinal

large-similarity-relation-Cardinal : Large-Similarity-Relation (_⊔_) Cardinal
large-similarity-relation-Cardinal =
  λ where
    .large-equivalence-relation-Large-Similarity-Relation →
      large-equivalence-relation-Cardinal
    .eq-sim-Large-Similarity-Relation →
      eq-sim-Cardinal
```

## External links

- [Cardinality](https://en.wikipedia.org/wiki/Cardinality) at Wikipedia
- [cardinal number](https://ncatlab.org/nlab/show/cardinal+number) at $n$Lab
