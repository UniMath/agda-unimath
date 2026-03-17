# Propositional truncation of binary relations

```agda
module foundation.propositional-truncation-binary-relations where
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

For any [binary relation](foundation.binary-relations.md) `R` on a type `A`,
there is an induced binary relation valued in propositions constructed by taking
the [propositional truncation](foundation.propositional-truncations.md) of `R`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  trunc-prop-Relation : Relation-Prop l2 A
  trunc-prop-Relation x y = trunc-Prop (R x y)

  type-trunc-prop-Relation : Relation l2 A
  type-trunc-prop-Relation = type-Relation-Prop trunc-prop-Relation
```

## Properties

### Reflexivity of the propositionally truncated relation

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  reflexive-trunc-prop-Relation :
    is-reflexive R → is-reflexive (type-trunc-prop-Relation R)
  reflexive-trunc-prop-Relation refl-R x = unit-trunc-Prop (refl-R x)
```

### Symmetry of the propositionally truncated relation

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  symmetric-trunc-prop-Relation :
    is-symmetric R → is-symmetric (type-trunc-prop-Relation R)
  symmetric-trunc-prop-Relation sym-R x y = map-trunc-Prop (sym-R x y)
```

### Transitivity of the propositionally truncated relation

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  transitive-trunc-prop-Relation :
    is-transitive R → is-transitive (type-trunc-prop-Relation R)
  transitive-trunc-prop-Relation trans-R x y z =
    map-binary-trunc-Prop (trans-R x y z)
```
