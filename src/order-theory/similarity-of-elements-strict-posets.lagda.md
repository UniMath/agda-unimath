# Similarity of elements in strict posets

```agda
module order-theory.similarity-of-elements-strict-posets where
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
open import order-theory.strict-posets
open import order-theory.strict-preorders
```

</details>

## Idea

Two elements `x` and `y` of a [strict poset](order-theory.strict-posets.md) `A`
are said to be
{{#concept "similar" Disambiguation="elements of a strict poset" Agda=sim-Strict-Poset}},
or **indiscernible**, if for every `z : A` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a strict poset" Agda=sim-from-below-Strict-Poset}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a strict poset" Agda=sim-from-above-Strict-Poset}}.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a strict poset `A`.

## Definitions

### Similarity from below of elements in strict posets

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  sim-from-below-Strict-Poset :
    (x y : type-Strict-Poset A) → UU (l1 ⊔ l2)
  sim-from-below-Strict-Poset =
    sim-from-below-Strict-Preorder (strict-preorder-Strict-Poset A)

  sim-from-below-prop-Strict-Poset :
    (x y : type-Strict-Poset A) → Prop (l1 ⊔ l2)
  sim-from-below-prop-Strict-Poset =
    sim-from-below-prop-Strict-Preorder (strict-preorder-Strict-Poset A)

  is-prop-sim-from-below-Strict-Poset :
    (x y : type-Strict-Poset A) → is-prop (sim-from-below-Strict-Poset x y)
  is-prop-sim-from-below-Strict-Poset =
    is-prop-sim-from-below-Strict-Preorder (strict-preorder-Strict-Poset A)
```

### Similarity from above of elements in strict posets

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  sim-from-above-Strict-Poset :
    (x y : type-Strict-Poset A) → UU (l1 ⊔ l2)
  sim-from-above-Strict-Poset =
    sim-from-above-Strict-Preorder (strict-preorder-Strict-Poset A)

  sim-from-above-prop-Strict-Poset :
    (x y : type-Strict-Poset A) → Prop (l1 ⊔ l2)
  sim-from-above-prop-Strict-Poset =
    sim-from-above-prop-Strict-Preorder (strict-preorder-Strict-Poset A)

  is-prop-sim-from-above-Strict-Poset :
    (x y : type-Strict-Poset A) → is-prop (sim-from-above-Strict-Poset x y)
  is-prop-sim-from-above-Strict-Poset =
    is-prop-sim-from-above-Strict-Preorder (strict-preorder-Strict-Poset A)
```

### Similarity of elements in strict posets

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  sim-Strict-Poset :
    (x y : type-Strict-Poset A) → UU (l1 ⊔ l2)
  sim-Strict-Poset =
    sim-Strict-Preorder (strict-preorder-Strict-Poset A)

  sim-prop-Strict-Poset :
    (x y : type-Strict-Poset A) → Prop (l1 ⊔ l2)
  sim-prop-Strict-Poset =
    sim-prop-Strict-Preorder (strict-preorder-Strict-Poset A)

  is-prop-sim-Strict-Poset :
    (x y : type-Strict-Poset A) → is-prop (sim-Strict-Poset x y)
  is-prop-sim-Strict-Poset =
    is-prop-sim-Strict-Preorder (strict-preorder-Strict-Poset A)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  refl-sim-from-below-Strict-Poset :
    is-reflexive (sim-from-below-Strict-Poset A)
  refl-sim-from-below-Strict-Poset =
    refl-sim-from-below-Strict-Preorder (strict-preorder-Strict-Poset A)

  refl-sim-from-above-Strict-Poset :
    is-reflexive (sim-from-above-Strict-Poset A)
  refl-sim-from-above-Strict-Poset =
    refl-sim-from-above-Strict-Preorder
      ( strict-preorder-Strict-Poset A)

  refl-sim-Strict-Poset :
    is-reflexive (sim-Strict-Poset A)
  refl-sim-Strict-Poset =
    refl-sim-Strict-Preorder (strict-preorder-Strict-Poset A)
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  transitive-sim-from-below-Strict-Poset :
    is-transitive (sim-from-below-Strict-Poset A)
  transitive-sim-from-below-Strict-Poset =
    transitive-sim-from-below-Strict-Preorder (strict-preorder-Strict-Poset A)

  transitive-sim-from-above-Strict-Poset :
    is-transitive (sim-from-above-Strict-Poset A)
  transitive-sim-from-above-Strict-Poset =
    transitive-sim-from-above-Strict-Preorder (strict-preorder-Strict-Poset A)

  transitive-sim-Strict-Poset :
    is-transitive (sim-Strict-Poset A)
  transitive-sim-Strict-Poset =
    transitive-sim-Strict-Preorder (strict-preorder-Strict-Poset A)
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (A : Strict-Poset l1 l2)
  where

  symmetric-sim-from-below-Strict-Poset :
    is-symmetric (sim-from-below-Strict-Poset A)
  symmetric-sim-from-below-Strict-Poset =
    symmetric-sim-from-below-Strict-Preorder (strict-preorder-Strict-Poset A)

  symmetric-sim-from-above-Strict-Poset :
    is-symmetric (sim-from-above-Strict-Poset A)
  symmetric-sim-from-above-Strict-Poset =
    symmetric-sim-from-above-Strict-Preorder (strict-preorder-Strict-Poset A)

  symmetric-sim-Strict-Poset :
    is-symmetric (sim-Strict-Poset A)
  symmetric-sim-Strict-Poset =
    symmetric-sim-Strict-Preorder (strict-preorder-Strict-Poset A)
```
