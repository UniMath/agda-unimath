# Induced large equivalence relations on large subtypes

```agda
module foundation.induced-large-equivalence-relations-large-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.induced-large-binary-relations-large-subtypes
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.large-subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [large subtype](foundation.large-subtypes.md) `S` of a
universe-polymorphic type `X : (l : Level) → UU (α l)`, any
[large equivalence relation](foundation.large-equivalence-relations.md) `R` on
`X` induces a large equivalence relation on `S`.

## Definition

```agda
module _
  {α β : Level → Level} {γ : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype β X)
  (R : Large-Equivalence-Relation γ X)
  where

  sim-prop-large-subtype-Large-Equivalence-Relation :
    Large-Relation-Prop γ (type-large-subtype S)
  sim-prop-large-subtype-Large-Equivalence-Relation =
    large-relation-prop-large-subtype
      ( S)
      ( sim-prop-Large-Equivalence-Relation R)

  sim-large-subtype-Large-Equivalence-Relation :
    Large-Relation γ (type-large-subtype S)
  sim-large-subtype-Large-Equivalence-Relation =
    large-relation-Large-Relation-Prop
      ( type-large-subtype S)
      ( sim-prop-large-subtype-Large-Equivalence-Relation)

  refl-sim-large-subtype-Large-Equivalence-Relation :
    is-reflexive-Large-Relation
      ( type-large-subtype S)
      ( sim-large-subtype-Large-Equivalence-Relation)
  refl-sim-large-subtype-Large-Equivalence-Relation =
    refl-large-relation-large-subtype
      ( S)
      ( sim-Large-Equivalence-Relation R)
      ( refl-sim-Large-Equivalence-Relation R)

  symmetric-sim-large-subtype-Large-Equivalence-Relation :
    is-symmetric-Large-Relation
      ( type-large-subtype S)
      ( sim-large-subtype-Large-Equivalence-Relation)
  symmetric-sim-large-subtype-Large-Equivalence-Relation =
    is-symmetric-large-relation-large-subtype
      ( S)
      ( sim-Large-Equivalence-Relation R)
      ( symmetric-sim-Large-Equivalence-Relation R)

  transitive-sim-large-subtype-Large-Equivalence-Relation :
    is-transitive-Large-Relation
      ( type-large-subtype S)
      ( sim-large-subtype-Large-Equivalence-Relation)
  transitive-sim-large-subtype-Large-Equivalence-Relation =
    is-transitive-large-relation-large-subtype
      ( S)
      ( sim-Large-Equivalence-Relation R)
      ( transitive-sim-Large-Equivalence-Relation R)

  large-equivalence-relation-large-subtype-Large-Equivalence-Relation :
    Large-Equivalence-Relation γ (type-large-subtype S)
  large-equivalence-relation-large-subtype-Large-Equivalence-Relation =
    make-Large-Equivalence-Relation
      ( sim-prop-large-subtype-Large-Equivalence-Relation)
      ( refl-sim-large-subtype-Large-Equivalence-Relation)
      ( symmetric-sim-large-subtype-Large-Equivalence-Relation)
      ( transitive-sim-large-subtype-Large-Equivalence-Relation)
```
