# Induced large similarity relations on large subtypes

```agda
module foundation.induced-large-similarity-relations-large-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.induced-large-equivalence-relations-large-subtypes
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.large-subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [large subtype](foundation.large-subtypes.md) `S` of a
universe-polymorphic type `X : (l : Level) → UU (α l)`, any
[large similarity relation](foundation.large-similarity-relations.md) `R` on `X`
induces a large similarity relation on `S`.

## Definition

```agda
module _
  {α β : Level → Level} {γ : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype β X)
  (R : Large-Similarity-Relation γ X)
  where

  large-equivalence-relation-large-subtype-Large-Similarity-Relation :
    Large-Equivalence-Relation γ (type-large-subtype S)
  large-equivalence-relation-large-subtype-Large-Similarity-Relation =
    large-equivalence-relation-large-subtype-Large-Equivalence-Relation
      ( S)
      ( large-equivalence-relation-Large-Similarity-Relation R)

  sim-large-subtype-Large-Similarity-Relation :
    Large-Relation γ (type-large-subtype S)
  sim-large-subtype-Large-Similarity-Relation =
    sim-Large-Equivalence-Relation
      ( large-equivalence-relation-large-subtype-Large-Similarity-Relation)

  eq-sim-large-subtype-Large-Similarity-Relation :
    {l : Level} (x y : type-large-subtype S l) →
    sim-large-subtype-Large-Similarity-Relation x y → x ＝ y
  eq-sim-large-subtype-Large-Similarity-Relation (x , _) (y , _) x~y =
    eq-type-large-subtype S (eq-sim-Large-Similarity-Relation R x y x~y)

  large-similarity-relation-large-subtype-Large-Similarity-Relation :
    Large-Similarity-Relation γ (type-large-subtype S)
  large-similarity-relation-large-subtype-Large-Similarity-Relation =
    make-Large-Similarity-Relation
      ( large-equivalence-relation-large-subtype-Large-Similarity-Relation)
      ( eq-sim-large-subtype-Large-Similarity-Relation)
```
