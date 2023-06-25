# Large preorders

```agda
module order-theory.large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **large preorder** consists of types indexed by a universe levels, and an
ordering relation comparing objects of arbitrary universe levels. This level of
generality therefore accommodates the inclusion relation on subtypes of
different universe levels. Many preorders in agda-unimath naturally arise as
large preorders.

## Definition

```agda
record
  Large-Preorder (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Preorder
  field
    type-Large-Preorder : (l : Level) → UU (α l)
    leq-Large-Preorder-Prop : Large-Relation-Prop α β type-Large-Preorder
    refl-leq-Large-Preorder :
      is-large-reflexive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-Large-Preorder-Prop)
    transitive-leq-Large-Preorder :
      is-large-transitive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-Large-Preorder-Prop)

open Large-Preorder public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Preorder α β)
  where

  leq-Large-Preorder : Large-Relation α β (type-Large-Preorder X)
  leq-Large-Preorder =
    type-Large-Relation-Prop
      ( type-Large-Preorder X)
      ( leq-Large-Preorder-Prop X)

  is-prop-leq-Large-Preorder :
    is-prop-Large-Relation (type-Large-Preorder X) (leq-Large-Preorder)
  is-prop-leq-Large-Preorder =
    is-prop-type-Large-Relation-Prop
      ( type-Large-Preorder X)
      ( leq-Large-Preorder-Prop X)

  leq-eq-Large-Preorder :
    {l1 : Level}
    {x y : type-Large-Preorder X l1} →
    (x ＝ y) → leq-Large-Preorder x y
  leq-eq-Large-Preorder {x = x} refl = refl-leq-Large-Preorder X x

  preorder-Large-Preorder : (l : Level) → Preorder (α l) (β l l)
  pr1 (preorder-Large-Preorder l) = type-Large-Preorder X l
  pr1 (pr2 (preorder-Large-Preorder l)) = leq-Large-Preorder-Prop X
  pr1 (pr2 (pr2 (preorder-Large-Preorder l))) = refl-leq-Large-Preorder X
  pr2 (pr2 (pr2 (preorder-Large-Preorder l))) = transitive-leq-Large-Preorder X
```
