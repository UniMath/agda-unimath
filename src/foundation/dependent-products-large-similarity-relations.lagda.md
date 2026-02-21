# Dependent products of large similarity relations

```agda
module foundation.dependent-products-large-similarity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-large-equivalence-relations
open import foundation.function-extensionality
open import foundation.large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

The [dependent product](foundation.dependent-products-large-binary-relations.md)
of a family of
[large similarity relations](foundation.large-similarity-relations.md) is a
large similarity relation.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  (R : (i : I) → Large-Similarity-Relation β (X i))
  where

  Π-Large-Similarity-Relation :
    Large-Similarity-Relation (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → (i : I) → X i l)
  Π-Large-Similarity-Relation =
    λ where
      .large-equivalence-relation-Large-Similarity-Relation →
        Π-Large-Equivalence-Relation I X
          ( λ i → large-equivalence-relation-Large-Similarity-Relation (R i))
      .eq-sim-Large-Similarity-Relation x y x~y →
        eq-htpy
          ( λ i → eq-sim-Large-Similarity-Relation (R i) (x i) (y i) (x~y i))
```
