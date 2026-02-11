# Truncations of binary relations

```agda
module foundation.truncation-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

Given a [binary relation](foundation.binary-relations.md) `R` on a type `A`, its
{{#concept "propositional truncation" Disambiguation="of a binary relation" Agda=trunc-Relation}}
is a relation valued in propositions.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  trunc-Relation : Relation-Prop l2 A
  trunc-Relation a b = trunc-Prop (R a b)

  type-trunc-Relation : Relation l2 A
  type-trunc-Relation = type-Relation-Prop trunc-Relation
```

## Properties

### Truncation preserves reflexivity

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  is-reflexive-trunc-Relation :
    is-reflexive R → is-reflexive-Relation-Prop (trunc-Relation R)
  is-reflexive-trunc-Relation H x = unit-trunc-Prop (H x)
```

### Truncation preserves symmetry

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  is-symmetric-trunc-Relation :
    is-symmetric R → is-symmetric-Relation-Prop (trunc-Relation R)
  is-symmetric-trunc-Relation H x y = map-trunc-Prop (H x y)
```

### Truncation preserves transitivity

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  is-transitive-trunc-Relation :
    is-transitive R → is-transitive-Relation-Prop (trunc-Relation R)
  is-transitive-trunc-Relation H x y z = map-binary-trunc-Prop (H x y z)
```
