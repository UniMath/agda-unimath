# Decidable relations on types

```agda
module foundation.decidable-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Idea

A **decidable (binary) relation** on `X` is a binary relation `R` on `X` such
that each `R x y` is a decidable proposition.

## Definitions

### Decidable relations

```agda
is-decidable-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → UU (l1 ⊔ l2)
is-decidable-Relation-Prop {A = A} R =
  (x y : A) → is-decidable ( rel-Relation-Prop R x y)

Decidable-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Relation l2 X = X → X → Decidable-Prop l2

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Relation l2 X)
  where

  relation-Decidable-Relation : X → X → Prop l2
  relation-Decidable-Relation x y = prop-Decidable-Prop (R x y)

  rel-Decidable-Relation : X → X → UU l2
  rel-Decidable-Relation x y = type-Decidable-Prop (R x y)

  is-prop-rel-Decidable-Relation :
    (x y : X) → is-prop (rel-Decidable-Relation x y)
  is-prop-rel-Decidable-Relation x y = is-prop-type-Decidable-Prop (R x y)

  is-decidable-Decidable-Relation :
    (x y : X) → is-decidable (rel-Decidable-Relation x y)
  is-decidable-Decidable-Relation x y =
    is-decidable-Decidable-Prop (R x y)

map-inv-equiv-relation-is-decidable-Decidable-Relation :
  {l1 l2 : Level} {X : UU l1} →
  Σ ( Relation-Prop l2 X) (λ R → is-decidable-Relation-Prop R) →
  Decidable-Relation l2 X
map-inv-equiv-relation-is-decidable-Decidable-Relation (R , d) x y =
  ( ( rel-Relation-Prop R x y) ,
    ( is-prop-rel-Relation-Prop R x y) ,
    ( d x y))

equiv-relation-is-decidable-Decidable-Relation :
  {l1 l2 : Level} {X : UU l1} →
  Decidable-Relation l2 X ≃
  Σ ( Relation-Prop l2 X) (λ R → is-decidable-Relation-Prop R)
pr1 equiv-relation-is-decidable-Decidable-Relation dec-R =
  ( relation-Decidable-Relation dec-R ,
    is-decidable-Decidable-Relation dec-R)
pr2 equiv-relation-is-decidable-Decidable-Relation =
  is-equiv-is-invertible
    ( map-inv-equiv-relation-is-decidable-Decidable-Relation)
    ( refl-htpy)
    ( refl-htpy)
```
