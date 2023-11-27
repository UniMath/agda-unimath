# Preorders

```agda
module order-theory.preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **preorder** is a type equipped with a reflexive, transitive relation that is
valued in propositions.

## Definition

```agda
Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder l1 l2 =
  Σ ( UU l1)
    ( λ X →
      Σ ( Relation-Prop l2 X)
        ( λ R →
          ( is-reflexive (type-Relation-Prop R)) ×
          ( is-transitive (type-Relation-Prop R))))

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  type-Preorder : UU l1
  type-Preorder = pr1 X

  leq-Preorder-Prop : Relation-Prop l2 type-Preorder
  leq-Preorder-Prop = pr1 (pr2 X)

  leq-Preorder : (x y : type-Preorder) → UU l2
  leq-Preorder x y = type-Prop (leq-Preorder-Prop x y)

  is-prop-leq-Preorder : (x y : type-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder = is-prop-type-Relation-Prop leq-Preorder-Prop

  concatenate-eq-leq-Preorder :
    {x y z : type-Preorder} → x ＝ y → leq-Preorder y z → leq-Preorder x z
  concatenate-eq-leq-Preorder refl = id

  concatenate-leq-eq-Preorder :
    {x y z : type-Preorder} → leq-Preorder x y → y ＝ z → leq-Preorder x z
  concatenate-leq-eq-Preorder H refl = H

  le-Preorder-Prop : Relation-Prop (l1 ⊔ l2) type-Preorder
  le-Preorder-Prop x y =
    prod-Prop (x ≠ y , is-prop-neg) (leq-Preorder-Prop x y)

  le-Preorder : Relation (l1 ⊔ l2) type-Preorder
  le-Preorder x y = type-Prop (le-Preorder-Prop x y)

  is-prop-le-Preorder : (x y : type-Preorder) → is-prop (le-Preorder x y)
  is-prop-le-Preorder = is-prop-type-Relation-Prop le-Preorder-Prop

  is-reflexive-leq-Preorder : is-reflexive (leq-Preorder)
  is-reflexive-leq-Preorder = pr1 (pr2 (pr2 X))

  refl-leq-Preorder : is-reflexive leq-Preorder
  refl-leq-Preorder = is-reflexive-leq-Preorder

  is-transitive-leq-Preorder : is-transitive leq-Preorder
  is-transitive-leq-Preorder = pr2 (pr2 (pr2 X))

  transitive-leq-Preorder : is-transitive leq-Preorder
  transitive-leq-Preorder = is-transitive-leq-Preorder
```

## Reasoning with inequalities in preorders

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Preorder X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Preorder X
    ≤ z
      by ineq-2
      in-Preorder X
    ≤ v
      by ineq-3
      in-Preorder X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Preorder_chain-of-inequalities_
infixl 0 step-calculate-in-Preorder

calculate-in-Preorder_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Preorder l1 l2)
  (x : type-Preorder X) → leq-Preorder X x x
calculate-in-Preorder_chain-of-inequalities_ = refl-leq-Preorder

step-calculate-in-Preorder :
  {l1 l2 : Level} (X : Preorder l1 l2)
  {x y : type-Preorder X} → leq-Preorder X x y →
  (z : type-Preorder X) → leq-Preorder X y z → leq-Preorder X x z
step-calculate-in-Preorder X {x} {y} u z v =
  is-transitive-leq-Preorder X x y z v u

syntax step-calculate-in-Preorder X u z v = u ≤ z by v in-Preorder X
```

## Properties

### Preorders are precategories whose hom-sets are propositions

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  precategory-Preorder : Precategory l1 l2
  pr1 precategory-Preorder = type-Preorder X
  pr1 (pr2 precategory-Preorder) x y = set-Prop (leq-Preorder-Prop X x y)
  pr1 (pr1 (pr2 (pr2 precategory-Preorder))) {x} {y} {z} =
    is-transitive-leq-Preorder X x y z
  pr1 (pr2 (pr1 (pr2 (pr2 precategory-Preorder))) {x} {y} {z} {w} h g f) =
    eq-is-prop (is-prop-type-Prop (leq-Preorder-Prop X x w))
  pr2 (pr2 (pr1 (pr2 (pr2 precategory-Preorder))) {x} {y} {z} {w} h g f) =
    eq-is-prop (is-prop-type-Prop (leq-Preorder-Prop X x w))
  pr1 (pr2 (pr2 (pr2 precategory-Preorder))) = refl-leq-Preorder X
  pr1 (pr2 (pr2 (pr2 (pr2 precategory-Preorder)))) {x} {y} f =
    eq-is-prop (is-prop-type-Prop (leq-Preorder-Prop X x y))
  pr2 (pr2 (pr2 (pr2 (pr2 precategory-Preorder)))) {x} {y} f =
    eq-is-prop (is-prop-type-Prop (leq-Preorder-Prop X x y))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  ( is-prop-hom-C : (x y : obj-Precategory C) → is-prop (hom-Precategory C x y))
  where

  preorder-is-prop-hom-Precategory : Preorder l1 l2
  pr1 preorder-is-prop-hom-Precategory =
    obj-Precategory C
  pr1 (pr1 (pr2 preorder-is-prop-hom-Precategory) x y) =
    hom-Precategory C x y
  pr2 (pr1 (pr2 preorder-is-prop-hom-Precategory) x y) =
    is-prop-hom-C x y
  pr1 (pr2 (pr2 preorder-is-prop-hom-Precategory)) x =
    id-hom-Precategory C
  pr2 (pr2 (pr2 preorder-is-prop-hom-Precategory)) x y z =
    comp-hom-Precategory C
```

It remains to show that these constructions form inverses to eachother.
