# Large posets

```agda
module order-theory.large-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

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

A **large poset** is a [large preorder](order-theory.large-preorders.md) such
that the restriction of the ordering relation to any particular universe level
is antisymmetric.

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
```

## Properties

### Small posets from large posets

```agda
  preorder-Large-Poset : (l : Level) → Preorder (α l) (β l l)
  preorder-Large-Poset = preorder-Large-Preorder (large-preorder-Large-Poset X)

  poset-Large-Poset : (l : Level) → Poset (α l) (β l l)
  pr1 (poset-Large-Poset l) = preorder-Large-Poset l
  pr2 (poset-Large-Poset l) = antisymmetric-leq-Large-Poset X

  set-Large-Poset : (l : Level) → Set (α l)
  set-Large-Poset l = set-Poset (poset-Large-Poset l)

  is-set-type-Large-Poset : {l : Level} → is-set (type-Large-Poset l)
  is-set-type-Large-Poset {l} = is-set-type-Poset (poset-Large-Poset l)
```

### Large posets are large categories

```agda
  large-precategory-Large-Poset : Large-Precategory α β
  large-precategory-Large-Poset =
    large-precategory-Large-Preorder (large-preorder-Large-Poset X)

  precategory-Large-Poset : (l : Level) → Precategory (α l) (β l l)
  precategory-Large-Poset =
    precategory-Large-Precategory large-precategory-Large-Poset

  is-large-category-Large-Poset :
    is-large-category-Large-Precategory large-precategory-Large-Poset
  is-large-category-Large-Poset {l} x y =
    is-equiv-is-prop
      ( is-set-type-Large-Poset x y)
      ( is-prop-iso-Precategory
        ( precategory-Large-Poset l) x y (is-prop-leq-Large-Poset x y))
      ( λ f →
        antisymmetric-leq-Large-Poset X x y
        ( hom-iso-Precategory (precategory-Large-Poset l) f)
        ( hom-inv-iso-Precategory (precategory-Large-Poset l) f))

  large-category-Large-Poset : Large-Category α β
  large-precategory-Large-Category large-category-Large-Poset =
    large-precategory-Large-Poset
  is-large-category-Large-Category large-category-Large-Poset =
    is-large-category-Large-Poset
```
