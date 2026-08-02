# Dependent products of equivalence relations

```agda
module foundation.dependent-products-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.dependent-products-binary-relations
open import foundation.equivalence-relations
open import foundation.function-types
open import foundation.universe-levels
```

</details>

## Idea

The [dependent product](foundation.dependent-products-binary-relations.md) of a
family of [equivalence relations](foundation.equivalence-relations.md) is an
equivalence relation.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  (R : (i : I) → equivalence-relation l3 (A i))
  where

  prop-Π-equivalence-relation : Relation-Prop (l1 ⊔ l3) ((i : I) → A i)
  prop-Π-equivalence-relation =
    Π-Relation-Prop I (prop-equivalence-relation ∘ R)

  sim-Π-equivalence-relation : Relation (l1 ⊔ l3) ((i : I) → A i)
  sim-Π-equivalence-relation =
    type-Relation-Prop prop-Π-equivalence-relation

  abstract
    is-reflexive-Π-equivalence-relation :
      is-reflexive sim-Π-equivalence-relation
    is-reflexive-Π-equivalence-relation =
      is-reflexive-Π-Relation I
        ( sim-equivalence-relation ∘ R)
        ( refl-equivalence-relation ∘ R)

    is-symmetric-Π-equivalence-relation :
      is-symmetric sim-Π-equivalence-relation
    is-symmetric-Π-equivalence-relation =
      is-symmetric-Π-Relation I
        ( sim-equivalence-relation ∘ R)
        ( symmetric-equivalence-relation ∘ R)

    is-transitive-Π-equivalence-relation :
      is-transitive sim-Π-equivalence-relation
    is-transitive-Π-equivalence-relation =
      is-transitive-Π-Relation I
        ( sim-equivalence-relation ∘ R)
        ( transitive-equivalence-relation ∘ R)

  Π-equivalence-relation : equivalence-relation (l1 ⊔ l3) ((i : I) → A i)
  Π-equivalence-relation =
    ( prop-Π-equivalence-relation ,
      is-reflexive-Π-equivalence-relation ,
      is-symmetric-Π-equivalence-relation ,
      is-transitive-Π-equivalence-relation)
```
