# Function large equivalence relations

```agda
module foundation.function-large-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-equivalence-relations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Given a [large equivalence relation](foundation.large-equivalence-relations.md)
on `X` and a type `A`, there is an induced large equivalence relation on
`A → X`.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (A : UU l1)
  (R : Large-Equivalence-Relation β X)
  where

  function-Large-Equivalence-Relation :
    Large-Equivalence-Relation
      ( λ l2 l3 → l1 ⊔ β l2 l3)
      ( λ l → A → X l)
  sim-prop-Large-Equivalence-Relation function-Large-Equivalence-Relation f g =
    Π-Prop A (λ a → sim-prop-Large-Equivalence-Relation R (f a) (g a))
  refl-sim-Large-Equivalence-Relation function-Large-Equivalence-Relation f a =
    refl-sim-Large-Equivalence-Relation R (f a)
  symmetric-sim-Large-Equivalence-Relation function-Large-Equivalence-Relation
    f g f~g a =
    symmetric-sim-Large-Equivalence-Relation R (f a) (g a) (f~g a)
  transitive-sim-Large-Equivalence-Relation function-Large-Equivalence-Relation
    f g h g~h f~g a =
    transitive-sim-Large-Equivalence-Relation
      ( R)
      ( f a)
      ( g a)
      ( h a)
      ( g~h a)
      ( f~g a)
```
