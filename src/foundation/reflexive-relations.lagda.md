# Reflexive relations

```agda
module foundation.reflexive-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A reflexive relation on a type `A` is a type-valued binary relation `R : A → A → U` equipped with a proof `r : (x : A) → R x x

## Definition

```agda
Reflexive-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Reflexive-Relation l2 A = Σ (Rel l2 A) (λ R → is-reflexive R)

module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  rel-Reflexive-Relation : Rel l2 A
  rel-Reflexive-Relation = pr1 R

  is-reflexive-Reflexive-Relation : is-reflexive rel-Reflexive-Relation
  is-reflexive-Reflexive-Relation = pr2 R
```
