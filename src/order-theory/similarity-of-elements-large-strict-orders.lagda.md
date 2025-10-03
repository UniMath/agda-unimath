# Similarity of elements in large strict orders

```agda
module order-theory.similarity-of-elements-large-strict-orders where
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

open import order-theory.large-strict-orders
open import order-theory.large-strict-preorders
open import order-theory.similarity-of-elements-large-strict-preorders
open import order-theory.strict-orders
```

</details>

## Idea

Two elements `x` and `y` of a
[large strict order](order-theory.large-strict-orders.md) `A` are said to be
{{#concept "similar" Disambiguation="elements of a large strict order" Agda=sim-Large-Strict-Order}},
or **indiscernible**, if for every `z : A` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a large strict order" Agda=sim-from-below-Large-Strict-Order}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a large strict order" Agda=sim-from-above-Large-Strict-Order}}.

**Notation.** In informal writing we will use the notation `x ≍ y` to assert
that `x` and `y` are similar elements in a large strict order `A`. The symbol
`≍` is the unicode symbol [Equivalent To](https://codepoints.net/U+224d)
(agda-input: `\asymp`).

## Definitions

### Similarity from below of elements in large strict orders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  sim-from-below-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    UU (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-Large-Strict-Order =
    sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-from-below-level-prop-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    Prop (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-prop-Large-Strict-Order =
    sim-from-below-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  is-prop-sim-from-below-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    is-prop (sim-from-below-level-Large-Strict-Order l x y)
  is-prop-sim-from-below-level-Large-Strict-Order =
    is-prop-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-from-below-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) → UUω
  sim-from-below-Large-Strict-Order =
    sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)
```

### Similarity from above of elements in large strict orders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  sim-from-above-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-Large-Strict-Order =
    sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-from-above-level-prop-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-prop-Large-Strict-Order =
    sim-from-above-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  is-prop-sim-from-above-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    is-prop (sim-from-above-level-Large-Strict-Order l x y)
  is-prop-sim-from-above-level-Large-Strict-Order =
    is-prop-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-from-above-Large-Strict-Order :
    {l1 l2 : Level} →
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) → UUω
  sim-from-above-Large-Strict-Order =
    sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)
```

### Similarity of elements in large strict orders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  sim-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-Large-Strict-Order =
    sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-level-prop-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-prop-Large-Strict-Order =
    sim-level-prop-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  is-prop-sim-level-Large-Strict-Order :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    is-prop (sim-level-Large-Strict-Order l x y)
  is-prop-sim-level-Large-Strict-Order =
    is-prop-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) → UUω
  sim-Large-Strict-Order =
    sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  sim-from-below-sim-Large-Strict-Order :
    {l1 l2 : Level}
    {x : type-Large-Strict-Order A l1}
    {y : type-Large-Strict-Order A l2} →
    sim-Large-Strict-Order x y →
    sim-from-below-Large-Strict-Order A x y
  sim-from-below-sim-Large-Strict-Order =
    sim-from-below-sim-Large-Strict-Preorder

  sim-from-above-sim-Large-Strict-Order :
    {l1 l2 : Level}
    {x : type-Large-Strict-Order A l1}
    {y : type-Large-Strict-Order A l2} →
    sim-Large-Strict-Order x y →
    sim-from-above-Large-Strict-Order A x y
  sim-from-above-sim-Large-Strict-Order =
    sim-from-above-sim-Large-Strict-Preorder
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  refl-sim-from-below-level-Large-Strict-Order :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-below-level-Large-Strict-Order A l)
  refl-sim-from-below-level-Large-Strict-Order =
    refl-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  refl-sim-from-below-Large-Strict-Order :
    {l1 : Level} (x : type-Large-Strict-Order A l1) →
    sim-from-below-Large-Strict-Order A x x
  refl-sim-from-below-Large-Strict-Order =
    refl-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  refl-sim-from-above-level-Large-Strict-Order :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-above-level-Large-Strict-Order A l)
  refl-sim-from-above-level-Large-Strict-Order =
    refl-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  refl-sim-from-above-Large-Strict-Order :
    {l1 : Level} (x : type-Large-Strict-Order A l1) →
    sim-from-above-Large-Strict-Order A x x
  refl-sim-from-above-Large-Strict-Order =
    refl-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  refl-sim-level-Large-Strict-Order :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-level-Large-Strict-Order A l)
  refl-sim-level-Large-Strict-Order =
    refl-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  refl-sim-Large-Strict-Order :
    {l1 : Level} (x : type-Large-Strict-Order A l1) →
    sim-Large-Strict-Order A x x
  refl-sim-Large-Strict-Order =
    refl-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)
```

### The similarity relation is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  transitive-sim-from-below-level-Large-Strict-Order :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-below-level-Large-Strict-Order A l)
  transitive-sim-from-below-level-Large-Strict-Order =
    transitive-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  transitive-sim-from-below-Large-Strict-Order :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2)
    (z : type-Large-Strict-Order A l3) →
    sim-from-below-Large-Strict-Order A y z →
    sim-from-below-Large-Strict-Order A x y →
    sim-from-below-Large-Strict-Order A x z
  transitive-sim-from-below-Large-Strict-Order =
    transitive-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  transitive-sim-from-above-level-Large-Strict-Order :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-above-level-Large-Strict-Order A l)
  transitive-sim-from-above-level-Large-Strict-Order =
    transitive-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  transitive-sim-from-above-Large-Strict-Order :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2)
    (z : type-Large-Strict-Order A l3) →
    sim-from-above-Large-Strict-Order A y z →
    sim-from-above-Large-Strict-Order A x y →
    sim-from-above-Large-Strict-Order A x z
  transitive-sim-from-above-Large-Strict-Order =
    transitive-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  transitive-sim-level-Large-Strict-Order :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-level-Large-Strict-Order A l)
  transitive-sim-level-Large-Strict-Order =
    transitive-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  transitive-sim-Large-Strict-Order :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2)
    (z : type-Large-Strict-Order A l3) →
    sim-Large-Strict-Order A y z →
    sim-Large-Strict-Order A x y →
    sim-Large-Strict-Order A x z
  transitive-sim-Large-Strict-Order =
    transitive-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)
```

### The similarity relation is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  symmetric-sim-from-below-level-Large-Strict-Order :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-below-level-Large-Strict-Order A l)
  symmetric-sim-from-below-level-Large-Strict-Order =
    symmetric-sim-from-below-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  symmetric-sim-from-below-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    sim-from-below-Large-Strict-Order A x y →
    sim-from-below-Large-Strict-Order A y x
  symmetric-sim-from-below-Large-Strict-Order =
    symmetric-sim-from-below-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  symmetric-sim-from-above-level-Large-Strict-Order :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-from-above-level-Large-Strict-Order A l)
  symmetric-sim-from-above-level-Large-Strict-Order =
    symmetric-sim-from-above-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  symmetric-sim-from-above-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    sim-from-above-Large-Strict-Order A x y →
    sim-from-above-Large-Strict-Order A y x
  symmetric-sim-from-above-Large-Strict-Order =
    symmetric-sim-from-above-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  symmetric-sim-level-Large-Strict-Order :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Order A)
      ( sim-level-Large-Strict-Order A l)
  symmetric-sim-level-Large-Strict-Order =
    symmetric-sim-level-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  symmetric-sim-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order A l1)
    (y : type-Large-Strict-Order A l2) →
    sim-Large-Strict-Order A x y →
    sim-Large-Strict-Order A y x
  symmetric-sim-Large-Strict-Order =
    symmetric-sim-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)
```
