# Products of equivalence relataions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.products-equivalence-relations
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.products-binary-relations funext univalence truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalence-relations funext univalence truncations
```

</details>

## Idea

Given two equivalence relations `R` and `S`, their product is an equivalence
relation.

## Definition

### The product of two equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  reflexive-product-Relation-Prop :
    is-reflexive-Relation-Prop
      ( product-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (reflexive-product-Relation-Prop x) = refl-equivalence-relation R (pr1 x)
  pr2 (reflexive-product-Relation-Prop x) = refl-equivalence-relation S (pr2 x)

  symmetric-product-Relation-Prop :
    is-symmetric-Relation-Prop
      ( product-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (symmetric-product-Relation-Prop x y (p , q)) =
    symmetric-equivalence-relation R (pr1 x) (pr1 y) p
  pr2 (symmetric-product-Relation-Prop x y (p , q)) =
    symmetric-equivalence-relation S (pr2 x) (pr2 y) q

  transitive-product-Relation-Prop :
    is-transitive-Relation-Prop
      ( product-Relation-Prop
        ( prop-equivalence-relation R)
        ( prop-equivalence-relation S))
  pr1 (transitive-product-Relation-Prop x y z (p , q) (p' , q')) =
    transitive-equivalence-relation R (pr1 x) (pr1 y) (pr1 z) p p'
  pr2 (transitive-product-Relation-Prop x y z (p , q) (p' , q')) =
    transitive-equivalence-relation S (pr2 x) (pr2 y) (pr2 z) q q'

  product-equivalence-relation : equivalence-relation (l2 ⊔ l4) (A × B)
  pr1 product-equivalence-relation =
    product-Relation-Prop
      ( prop-equivalence-relation R)
      ( prop-equivalence-relation S)
  pr1 (pr2 product-equivalence-relation) = reflexive-product-Relation-Prop
  pr1 (pr2 (pr2 product-equivalence-relation)) = symmetric-product-Relation-Prop
  pr2 (pr2 (pr2 product-equivalence-relation)) =
    transitive-product-Relation-Prop
```
