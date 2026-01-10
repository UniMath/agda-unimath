# Truncation of equivalence relations

```agda
module foundation.truncation-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.truncation-binary-relations
open import foundation.universe-levels
```

</details>

## Idea

Given a [relation](foundation.binary-relations.md) that is reflexive, symmetric,
and transitive, its
[propositional truncation](foundation.truncation-binary-relations.md) is an
[equivalence relation](foundation.equivalence-relations.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  (refl-R : is-reflexive R)
  (symmetric-R : is-symmetric R)
  (transitive-R : is-transitive R)
  where

  equivalence-relation-trunc-Relation : equivalence-relation l2 A
  equivalence-relation-trunc-Relation =
    ( trunc-Relation R ,
      is-reflexive-trunc-Relation R refl-R ,
      is-symmetric-trunc-Relation R symmetric-R ,
      is-transitive-trunc-Relation R transitive-R)
```
