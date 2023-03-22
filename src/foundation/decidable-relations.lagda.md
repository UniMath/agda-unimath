# Decidable relations on types

```agda
module foundation.decidable-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.decidable-propositions
<<<<<<< HEAD
=======
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.universe-levels
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

</details>

## Idea

A decidable (binary) relation on `X` is a binary relation `R` on `X` such that
each `R x y` is a decidable proposition

## Definitions

### Decidable relations

```agda
is-decidable-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-decidable-Rel-Prop {A = A} R =
  (x y : A) → is-decidable ( type-Rel-Prop R x y)

Decidable-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Relation l2 X = X → X → decidable-Prop l2

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Relation l2 X)
  where

  relation-Decidable-Relation : X → X → Prop l2
  relation-Decidable-Relation x y = prop-decidable-Prop (R x y)

  type-Decidable-Relation : X → X → UU l2
  type-Decidable-Relation x y = type-decidable-Prop (R x y)

  is-prop-type-Decidable-Relation :
    (x y : X) → is-prop (type-Decidable-Relation x y)
  is-prop-type-Decidable-Relation x y = is-prop-type-decidable-Prop (R x y)

  is-decidable-type-Decidable-Relation :
    (x y : X) → is-decidable (type-Decidable-Relation x y)
  is-decidable-type-Decidable-Relation x y =
    is-decidable-type-decidable-Prop (R x y)

<<<<<<< HEAD
=======
map-inv-equiv-relation-is-decidable-Decidable-Relation :
  {l1 l2 : Level} {X : UU l1} →
  Σ ( Rel-Prop l2 X) (λ R → is-decidable-Rel-Prop R) →
  Decidable-Relation l2 X
map-inv-equiv-relation-is-decidable-Decidable-Relation (R , d)  x y =
  ( ( type-Rel-Prop R x y) ,
    ( is-prop-type-Rel-Prop R x y) ,
    ( d x y))

>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
equiv-relation-is-decidable-Decidable-Relation :
  {l1 l2 : Level} {X : UU l1} →
  Decidable-Relation l2 X ≃
  Σ ( Rel-Prop l2 X) (λ R → is-decidable-Rel-Prop R)
pr1 equiv-relation-is-decidable-Decidable-Relation dec-R =
  ( relation-Decidable-Relation dec-R ,
    is-decidable-type-Decidable-Relation dec-R)
pr2 equiv-relation-is-decidable-Decidable-Relation =
  is-equiv-has-inverse
<<<<<<< HEAD
    ( λ R → (λ x y → (pr1 (pr1 R x y)) , ((pr2 (pr1 R x y)) , (pr2 R x y)) ) )
=======
    ( map-inv-equiv-relation-is-decidable-Decidable-Relation )
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    ( refl-htpy)
    ( refl-htpy)
```
