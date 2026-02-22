# Dependent products of large equivalence relations

```agda
module foundation.dependent-products-large-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-large-binary-relations
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.universe-levels
```

</details>

## Idea

The [dependent product](foundation.dependent-products-large-binary-relations.md)
of a family of
[large equivalence relations](foundation.large-equivalence-relations.md) is a
large equivalence relation.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  (R : (i : I) → Large-Equivalence-Relation β (X i))
  where

  Π-Large-Equivalence-Relation :
    Large-Equivalence-Relation (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → (i : I) → X i l)
  Π-Large-Equivalence-Relation =
    λ where
      .sim-prop-Large-Equivalence-Relation →
        Π-Large-Relation-Prop I X
          ( λ i → sim-prop-Large-Equivalence-Relation (R i))
      .refl-sim-Large-Equivalence-Relation →
        is-reflexive-Π-Large-Relation I X
          ( λ i → sim-Large-Equivalence-Relation (R i))
          ( λ i → refl-sim-Large-Equivalence-Relation (R i))
      .symmetric-sim-Large-Equivalence-Relation →
        is-symmetric-Π-Large-Relation I X
          ( λ i → sim-Large-Equivalence-Relation (R i))
          ( λ i → symmetric-sim-Large-Equivalence-Relation (R i))
      .transitive-sim-Large-Equivalence-Relation →
        is-transitive-Π-Large-Relation I X
          ( λ i → sim-Large-Equivalence-Relation (R i))
          ( λ i → transitive-sim-Large-Equivalence-Relation (R i))
```
