# Similarity of elements in large strict posets

```agda
module order-theory.similarity-of-elements-large-strict-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.large-strict-posets
open import order-theory.large-strict-preorders
open import order-theory.similarity-of-elements-large-strict-preorders
open import order-theory.strict-posets
```

</details>

## Idea

Two elements `x` and `y` of a
[large strict poset](order-theory.large-strict-posets.md) `A` are said to be
{{#concept "similar" Disambiguation="elements of a large strict poset" Agda=sim-Large-Strict-Poset}},
or **indiscernible**, if for every `z : A` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a large strict poset" Agda=sim-from-below-Large-Strict-Poset}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a large strict poset" Agda=sim-from-above-Large-Strict-Poset}}.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a large strict poset `A`.

## Definitions

### Similarity from below of elements in large strict posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  sim-from-below-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    UU (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-Large-Strict-Poset =
    sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-from-below-level-prop-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    Prop (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-prop-Large-Strict-Poset =
    sim-from-below-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  is-prop-sim-from-below-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    is-prop (sim-from-below-level-Large-Strict-Poset l x y)
  is-prop-sim-from-below-level-Large-Strict-Poset =
    is-prop-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-from-below-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) → UUω
  sim-from-below-Large-Strict-Poset =
    sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)
```

### Similarity from above of elements in large strict posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  sim-from-above-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-Large-Strict-Poset =
    sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-from-above-level-prop-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-prop-Large-Strict-Poset =
    sim-from-above-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  is-prop-sim-from-above-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    is-prop (sim-from-above-level-Large-Strict-Poset l x y)
  is-prop-sim-from-above-level-Large-Strict-Poset =
    is-prop-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-from-above-Large-Strict-Poset :
    {l1 l2 : Level} →
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) → UUω
  sim-from-above-Large-Strict-Poset =
    sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)
```

### Similarity of elements in large strict posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  sim-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-Large-Strict-Poset =
    sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-level-prop-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-prop-Large-Strict-Poset =
    sim-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  is-prop-sim-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    is-prop (sim-level-Large-Strict-Poset l x y)
  is-prop-sim-level-Large-Strict-Poset =
    is-prop-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) → UUω
  sim-Large-Strict-Poset =
    sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  sim-from-below-sim-Large-Strict-Poset :
    {l1 l2 : Level}
    {x : type-Large-Strict-Poset A l1}
    {y : type-Large-Strict-Poset A l2} →
    sim-Large-Strict-Poset x y →
    sim-from-below-Large-Strict-Poset A x y
  sim-from-below-sim-Large-Strict-Poset =
    sim-from-below-sim-Large-Strict-Preorder

  sim-from-above-sim-Large-Strict-Poset :
    {l1 l2 : Level}
    {x : type-Large-Strict-Poset A l1}
    {y : type-Large-Strict-Poset A l2} →
    sim-Large-Strict-Poset x y →
    sim-from-above-Large-Strict-Poset A x y
  sim-from-above-sim-Large-Strict-Poset =
    sim-from-above-sim-Large-Strict-Preorder
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  refl-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-below-level-Large-Strict-Poset A l)
  refl-sim-from-below-level-Large-Strict-Poset =
    refl-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  refl-sim-from-below-Large-Strict-Poset :
    {l1 : Level} (x : type-Large-Strict-Poset A l1) →
    sim-from-below-Large-Strict-Poset A x x
  refl-sim-from-below-Large-Strict-Poset =
    refl-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  refl-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-above-level-Large-Strict-Poset A l)
  refl-sim-from-above-level-Large-Strict-Poset =
    refl-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  refl-sim-from-above-Large-Strict-Poset :
    {l1 : Level} (x : type-Large-Strict-Poset A l1) →
    sim-from-above-Large-Strict-Poset A x x
  refl-sim-from-above-Large-Strict-Poset =
    refl-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  refl-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-level-Large-Strict-Poset A l)
  refl-sim-level-Large-Strict-Poset =
    refl-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  refl-sim-Large-Strict-Poset :
    {l1 : Level} (x : type-Large-Strict-Poset A l1) →
    sim-Large-Strict-Poset A x x
  refl-sim-Large-Strict-Poset =
    refl-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)
```

### The similarity relation is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  transitive-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-below-level-Large-Strict-Poset A l)
  transitive-sim-from-below-level-Large-Strict-Poset =
    transitive-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  transitive-sim-from-below-Large-Strict-Poset :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2)
    (z : type-Large-Strict-Poset A l3) →
    sim-from-below-Large-Strict-Poset A y z →
    sim-from-below-Large-Strict-Poset A x y →
    sim-from-below-Large-Strict-Poset A x z
  transitive-sim-from-below-Large-Strict-Poset =
    transitive-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  transitive-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-above-level-Large-Strict-Poset A l)
  transitive-sim-from-above-level-Large-Strict-Poset =
    transitive-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  transitive-sim-from-above-Large-Strict-Poset :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2)
    (z : type-Large-Strict-Poset A l3) →
    sim-from-above-Large-Strict-Poset A y z →
    sim-from-above-Large-Strict-Poset A x y →
    sim-from-above-Large-Strict-Poset A x z
  transitive-sim-from-above-Large-Strict-Poset =
    transitive-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  transitive-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-level-Large-Strict-Poset A l)
  transitive-sim-level-Large-Strict-Poset =
    transitive-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  transitive-sim-Large-Strict-Poset :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2)
    (z : type-Large-Strict-Poset A l3) →
    sim-Large-Strict-Poset A y z →
    sim-Large-Strict-Poset A x y →
    sim-Large-Strict-Poset A x z
  transitive-sim-Large-Strict-Poset =
    transitive-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)
```

### The similarity relation is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  symmetric-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-below-level-Large-Strict-Poset A l)
  symmetric-sim-from-below-level-Large-Strict-Poset =
    symmetric-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  symmetric-sim-from-below-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    sim-from-below-Large-Strict-Poset A x y →
    sim-from-below-Large-Strict-Poset A y x
  symmetric-sim-from-below-Large-Strict-Poset =
    symmetric-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  symmetric-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-from-above-level-Large-Strict-Poset A l)
  symmetric-sim-from-above-level-Large-Strict-Poset =
    symmetric-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  symmetric-sim-from-above-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    sim-from-above-Large-Strict-Poset A x y →
    sim-from-above-Large-Strict-Poset A y x
  symmetric-sim-from-above-Large-Strict-Poset =
    symmetric-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  symmetric-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset A)
      ( sim-level-Large-Strict-Poset A l)
  symmetric-sim-level-Large-Strict-Poset =
    symmetric-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  symmetric-sim-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset A l1)
    (y : type-Large-Strict-Poset A l2) →
    sim-Large-Strict-Poset A x y →
    sim-Large-Strict-Poset A y x
  symmetric-sim-Large-Strict-Poset =
    symmetric-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)
```
