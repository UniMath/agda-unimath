# Large posets

```agda
module order-theory.large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A **large poset** is a large preorder such that the restriction of the ordering
relation to any particular universe level is antisymmetric

## Definition

```agda
record
  Large-Poset (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Poset
  field
    large-preorder-Large-Poset : Large-Preorder α β
    antisymmetric-leq-Large-Poset :
      is-large-antisymmetric
        ( type-Large-Preorder large-preorder-Large-Poset)
        ( leq-Large-Preorder large-preorder-Large-Poset)

open Large-Poset public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Poset α β)
  where

  type-Large-Poset : (l : Level) → UU (α l)
  type-Large-Poset = type-Large-Preorder (large-preorder-Large-Poset X)

  leq-Large-Poset-Prop : Large-Relation-Prop α β (type-Large-Poset)
  leq-Large-Poset-Prop = leq-Large-Preorder-Prop (large-preorder-Large-Poset X)

  leq-Large-Poset : Large-Relation α β (type-Large-Poset)
  leq-Large-Poset = leq-Large-Preorder (large-preorder-Large-Poset X)

  is-prop-leq-Large-Poset :
    is-prop-Large-Relation (type-Large-Poset) (leq-Large-Poset)
  is-prop-leq-Large-Poset =
    is-prop-leq-Large-Preorder (large-preorder-Large-Poset X)

  leq-eq-Large-Poset :
    {l1 : Level} {x y : type-Large-Poset l1} →
    (x ＝ y) → leq-Large-Poset x y
  leq-eq-Large-Poset =
    leq-eq-Large-Preorder (large-preorder-Large-Poset X)

  refl-leq-Large-Poset : is-large-reflexive type-Large-Poset leq-Large-Poset
  refl-leq-Large-Poset = refl-leq-Large-Preorder (large-preorder-Large-Poset X)

  transitive-leq-Large-Poset :
    is-large-transitive type-Large-Poset leq-Large-Poset
  transitive-leq-Large-Poset =
    transitive-leq-Large-Preorder (large-preorder-Large-Poset X)

  preorder-Large-Poset : (l : Level) → Preorder (α l) (β l l)
  pr1 (preorder-Large-Poset l) = type-Large-Poset l
  pr1 (pr2 (preorder-Large-Poset l)) = leq-Large-Poset-Prop
  pr1 (pr2 (pr2 (preorder-Large-Poset l))) = refl-leq-Large-Poset
  pr2 (pr2 (pr2 (preorder-Large-Poset l))) = transitive-leq-Large-Poset

  poset-Large-Poset : (l : Level) → Poset (α l) (β l l)
  pr1 (poset-Large-Poset l) = preorder-Large-Poset l
  pr2 (poset-Large-Poset l) = antisymmetric-leq-Large-Poset X

  set-Large-Poset : (l : Level) → Set (α l)
  set-Large-Poset l = set-Poset (poset-Large-Poset l)

  is-set-type-Large-Poset : {l : Level} → is-set (type-Large-Poset l)
  is-set-type-Large-Poset {l} = is-set-type-Poset (poset-Large-Poset l)
```
