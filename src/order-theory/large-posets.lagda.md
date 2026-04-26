# Large posets

```agda
module order-theory.large-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
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

### Large posets

```agda
record
  Large-Poset (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Poset
  field
    large-preorder-Large-Poset : Large-Preorder α β
    antisymmetric-leq-Large-Poset :
      is-antisymmetric-Large-Relation
        ( type-Large-Preorder large-preorder-Large-Poset)
        ( leq-Large-Preorder large-preorder-Large-Poset)

open Large-Poset public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Poset α β)
  where

  type-Large-Poset : (l : Level) → UU (α l)
  type-Large-Poset = type-Large-Preorder (large-preorder-Large-Poset X)

  leq-prop-Large-Poset : Large-Relation-Prop β (type-Large-Poset)
  leq-prop-Large-Poset = leq-prop-Large-Preorder (large-preorder-Large-Poset X)

  leq-Large-Poset : Large-Relation β (type-Large-Poset)
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

  refl-leq-Large-Poset :
    is-reflexive-Large-Relation type-Large-Poset leq-Large-Poset
  refl-leq-Large-Poset =
    refl-leq-Large-Preorder (large-preorder-Large-Poset X)

  transitive-leq-Large-Poset :
    is-transitive-Large-Relation type-Large-Poset leq-Large-Poset
  transitive-leq-Large-Poset =
    transitive-leq-Large-Preorder (large-preorder-Large-Poset X)
```

### The predicate on large categories of being a large poset

A [large category](category-theory.large-categories.md) is said to be a **large
poset** if `hom X Y` is a proposition for every two objects `X` and `Y`.

**Lemma**. _Any large category of which the hom-[sets](foundation-core.sets.md)
are [propositions](foundation-core.propositions.md) is a large poset._

**Proof:** The condition that `C` is a large poset immediately gives us a
[large precategory](category-theory.large-precategories.md). The interesting
part of the claim is therefore that this large preorder is antisymmetric.

Consider two objects `X` and `Y` in `C`, and two morphisms `f : X → Y` and
`g : Y → X`. Since there is at most one morphism between any two objects, it
follows immediately that `f ∘ g ＝ id` and `g ∘ f ＝ id`. Therefore we have an
isomorphism `f : X ≅ Y`. Since `C` was assumed to be a category, this implies
that `X ＝ Y`.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  is-large-poset-Large-Category : UUω
  is-large-poset-Large-Category =
    is-large-preorder-Large-Precategory (large-precategory-Large-Category C)

  is-antisymmetric-is-large-poset-Large-Category :
    is-large-poset-Large-Category →
    is-antisymmetric-Large-Relation
      ( obj-Large-Category C)
      ( hom-Large-Category C)
  is-antisymmetric-is-large-poset-Large-Category H X Y f g =
    eq-iso-Large-Category C X Y
      ( f , g , eq-is-prop (H Y Y) , eq-is-prop (H X X))

  large-poset-Large-Category :
    is-large-poset-Large-Category → Large-Poset α β
  large-preorder-Large-Poset (large-poset-Large-Category H) =
    large-preorder-Large-Precategory (large-precategory-Large-Category C) H
  antisymmetric-leq-Large-Poset (large-poset-Large-Category H) =
    is-antisymmetric-is-large-poset-Large-Category H
```

### Small posets from large posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Poset α β)
  where

  preorder-Large-Poset : (l : Level) → Preorder (α l) (β l l)
  preorder-Large-Poset = preorder-Large-Preorder (large-preorder-Large-Poset X)

  poset-Large-Poset : (l : Level) → Poset (α l) (β l l)
  pr1 (poset-Large-Poset l) = preorder-Large-Poset l
  pr2 (poset-Large-Poset l) = antisymmetric-leq-Large-Poset X

  set-Large-Poset : (l : Level) → Set (α l)
  set-Large-Poset l = set-Poset (poset-Large-Poset l)

  is-set-type-Large-Poset : {l : Level} → is-set (type-Large-Poset X l)
  is-set-type-Large-Poset {l} = is-set-type-Poset (poset-Large-Poset l)
```

## Properties

### Large posets are large categories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  large-precategory-Large-Poset : Large-Precategory α β
  large-precategory-Large-Poset =
    large-precategory-Large-Preorder (large-preorder-Large-Poset P)

  precategory-Large-Poset : (l : Level) → Precategory (α l) (β l l)
  precategory-Large-Poset =
    precategory-Large-Precategory large-precategory-Large-Poset

  is-large-category-Large-Poset :
    is-large-category-Large-Precategory large-precategory-Large-Poset
  is-large-category-Large-Poset {l} x y =
    is-equiv-has-converse-is-prop
      ( is-set-type-Large-Poset P x y)
      ( is-prop-iso-is-prop-hom-Precategory
        ( precategory-Large-Poset l)
        ( is-prop-leq-Large-Poset P x y))
      ( λ f →
        antisymmetric-leq-Large-Poset P x y
        ( hom-iso-Precategory (precategory-Large-Poset l) f)
        ( hom-inv-iso-Precategory (precategory-Large-Poset l) f))

  large-category-Large-Poset : Large-Category α β
  large-precategory-Large-Category large-category-Large-Poset =
    large-precategory-Large-Poset
  is-large-category-Large-Category large-category-Large-Poset =
    is-large-category-Large-Poset

  is-large-poset-large-category-Large-Poset :
    is-large-poset-Large-Category large-category-Large-Poset
  is-large-poset-large-category-Large-Poset =
    is-prop-leq-Large-Poset P
```

## Reasoning with inequalities in large posets

Inequalities in large posets can be constructed by equational reasoning as
follows:

```text
let open inequality-reasoning-Poset X
in
  chain-of-inequalities
  x ≤ y
      by ineq-1
    ≤ z
      by ineq-2
    ≤ v
      by ineq-3
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
module inequality-reasoning-Large-Poset
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  infixl 1 chain-of-inequalities_
  infixl 0 step-calculate-in-Large-Poset

  chain-of-inequalities_ :
    {l : Level} (x : type-Large-Poset P l) → leq-Large-Poset P x x
  chain-of-inequalities_ = refl-leq-Large-Poset P

  step-calculate-in-Large-Poset :
    {l1 l2 : Level} {x : type-Large-Poset P l1} {y : type-Large-Poset P l2} →
    leq-Large-Poset P x y →
    {l3 : Level} (z : type-Large-Poset P l3) →
    leq-Large-Poset P y z → leq-Large-Poset P x z
  step-calculate-in-Large-Poset {x = x} {y = y} u z v =
    transitive-leq-Large-Poset P x y z v u

  syntax step-calculate-in-Large-Poset u z v = u ≤ z by v
```
