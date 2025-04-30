# Similarity of elements in strict orders

```agda
module order-theory.similarity-of-elements-strict-orders where
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
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.similarity-of-elements-strict-preorders
open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

Two elements `x` and `y` of a [strict order](order-theory.strict-orders.md) `A`
are said to be
{{#concept "similar" Disambiguation="elements of a strict order" Agda=sim-Strict-Order}},
or **indiscernible**, if for every `z : A` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a strict order" Agda=sim-from-below-Strict-Order}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a strict order" Agda=sim-from-above-Strict-Order}}.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a strict order `A`.

## Definitions

### Similarity from below of elements in strict orders

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  sim-from-below-Strict-Order :
    (x y : type-Strict-Order A) → UU (l1 ⊔ l2)
  sim-from-below-Strict-Order =
    sim-from-below-Strict-Preorder (strict-preorder-Strict-Order A)

  sim-from-below-prop-Strict-Order :
    (x y : type-Strict-Order A) → Prop (l1 ⊔ l2)
  sim-from-below-prop-Strict-Order =
    sim-from-below-prop-Strict-Preorder (strict-preorder-Strict-Order A)

  is-prop-sim-from-below-Strict-Order :
    (x y : type-Strict-Order A) → is-prop (sim-from-below-Strict-Order x y)
  is-prop-sim-from-below-Strict-Order =
    is-prop-sim-from-below-Strict-Preorder (strict-preorder-Strict-Order A)
```

### Similarity from above of elements in strict orders

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  sim-from-above-Strict-Order :
    (x y : type-Strict-Order A) → UU (l1 ⊔ l2)
  sim-from-above-Strict-Order =
    sim-from-above-Strict-Preorder (strict-preorder-Strict-Order A)

  sim-from-above-prop-Strict-Order :
    (x y : type-Strict-Order A) → Prop (l1 ⊔ l2)
  sim-from-above-prop-Strict-Order =
    sim-from-above-prop-Strict-Preorder (strict-preorder-Strict-Order A)

  is-prop-sim-from-above-Strict-Order :
    (x y : type-Strict-Order A) → is-prop (sim-from-above-Strict-Order x y)
  is-prop-sim-from-above-Strict-Order =
    is-prop-sim-from-above-Strict-Preorder (strict-preorder-Strict-Order A)
```

### Similarity of elements in strict orders

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  sim-Strict-Order :
    (x y : type-Strict-Order A) → UU (l1 ⊔ l2)
  sim-Strict-Order =
    sim-Strict-Preorder (strict-preorder-Strict-Order A)

  sim-prop-Strict-Order :
    (x y : type-Strict-Order A) → Prop (l1 ⊔ l2)
  sim-prop-Strict-Order =
    sim-prop-Strict-Preorder (strict-preorder-Strict-Order A)

  is-prop-sim-Strict-Order :
    (x y : type-Strict-Order A) → is-prop (sim-Strict-Order x y)
  is-prop-sim-Strict-Order =
    is-prop-sim-Strict-Preorder (strict-preorder-Strict-Order A)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  refl-sim-from-below-Strict-Order :
    is-reflexive (sim-from-below-Strict-Order A)
  refl-sim-from-below-Strict-Order =
    refl-sim-from-below-Strict-Preorder (strict-preorder-Strict-Order A)

  refl-sim-from-above-Strict-Order :
    is-reflexive (sim-from-above-Strict-Order A)
  refl-sim-from-above-Strict-Order =
    refl-sim-from-above-Strict-Preorder
      ( strict-preorder-Strict-Order A)

  refl-sim-Strict-Order :
    is-reflexive (sim-Strict-Order A)
  refl-sim-Strict-Order =
    refl-sim-Strict-Preorder (strict-preorder-Strict-Order A)
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  transitive-sim-from-below-Strict-Order :
    is-transitive (sim-from-below-Strict-Order A)
  transitive-sim-from-below-Strict-Order =
    transitive-sim-from-below-Strict-Preorder (strict-preorder-Strict-Order A)

  transitive-sim-from-above-Strict-Order :
    is-transitive (sim-from-above-Strict-Order A)
  transitive-sim-from-above-Strict-Order =
    transitive-sim-from-above-Strict-Preorder (strict-preorder-Strict-Order A)

  transitive-sim-Strict-Order :
    is-transitive (sim-Strict-Order A)
  transitive-sim-Strict-Order =
    transitive-sim-Strict-Preorder (strict-preorder-Strict-Order A)
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (A : Strict-Order l1 l2)
  where

  symmetric-sim-from-below-Strict-Order :
    is-symmetric (sim-from-below-Strict-Order A)
  symmetric-sim-from-below-Strict-Order =
    symmetric-sim-from-below-Strict-Preorder (strict-preorder-Strict-Order A)

  symmetric-sim-from-above-Strict-Order :
    is-symmetric (sim-from-above-Strict-Order A)
  symmetric-sim-from-above-Strict-Order =
    symmetric-sim-from-above-Strict-Preorder (strict-preorder-Strict-Order A)

  symmetric-sim-Strict-Order :
    is-symmetric (sim-Strict-Order A)
  symmetric-sim-Strict-Order =
    symmetric-sim-Strict-Preorder (strict-preorder-Strict-Order A)
```
