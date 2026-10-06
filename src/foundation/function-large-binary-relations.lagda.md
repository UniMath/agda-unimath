# Function large binary relations

```agda
module foundation.function-large-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-large-binary-relations
open import foundation.large-binary-relations
open import foundation.universe-levels
```

</details>

## Idea

Given a [large binary relation](foundation.large-binary-relations.md) on a
family of types `X` stratified by
[universe levels](foundation.universe-levels.md), there is an induced large
binary relation on functions `I → X`.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  {X : (l : Level) → UU (α l)}
  where

  function-Large-Relation :
    Large-Relation β X → Large-Relation (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → I → X l)
  function-Large-Relation R = Π-Large-Relation I (λ _ → X) (λ _ → R)

  function-Large-Relation-Prop :
    Large-Relation-Prop β X →
    Large-Relation-Prop (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → I → X l)
  function-Large-Relation-Prop R =
    Π-Large-Relation-Prop I (λ _ → X) (λ _ → R)
```
