# Products of equivalence relataions

```agda
module foundation.products-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.products-binary-relations

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.universe-levels
```

</details>

## Idea

Given two equivalence relations `R` and `S`, their product is an equivalence relation.

## Definition

### The product of two equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  where

  reflexive-prod-Rel-Prop :
    is-reflexive-Rel-Prop
      ( prod-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S))
  pr1 (reflexive-prod-Rel-Prop) = refl-Eq-Rel R
  pr2 (reflexive-prod-Rel-Prop) = refl-Eq-Rel S

  symmetric-prod-Rel-Prop :
    is-symmetric-Rel-Prop
      ( prod-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S))
  pr1 (symmetric-prod-Rel-Prop (p , q)) = symm-Eq-Rel R p
  pr2 (symmetric-prod-Rel-Prop (p , q)) = symm-Eq-Rel S q

  transitive-prod-Rel-Prop :
    is-transitive-Rel-Prop
      ( prod-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S))
  pr1 (transitive-prod-Rel-Prop (p , q) (p' , q')) = trans-Eq-Rel R p p'
  pr2 (transitive-prod-Rel-Prop (p , q) (p' , q')) = trans-Eq-Rel S q q'

  prod-Eq-Rel :
    Eq-Rel (l2 ⊔ l4) (A × B)
  pr1 prod-Eq-Rel = prod-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S)
  pr1 (pr2 prod-Eq-Rel) = reflexive-prod-Rel-Prop
  pr1 (pr2 (pr2 prod-Eq-Rel)) = symmetric-prod-Rel-Prop
  pr2 (pr2 (pr2 prod-Eq-Rel)) = transitive-prod-Rel-Prop
```
