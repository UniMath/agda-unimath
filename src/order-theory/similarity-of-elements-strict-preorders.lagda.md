# Similarity of elements in strict preorders

```agda
module order-theory.similarity-of-elements-strict-preorders where
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

open import order-theory.strict-preorders
```

</details>

## Idea

Two elements `x` and `y` of a
[strict preorder](order-theory.strict-preorders.md) `P` are said to be
{{#concept "similar" Disambiguation="elements of a strict preorder" Agda=sim-Strict-Preorder}},
or **indiscernible**, if for every `z : P` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a strict preorder" Agda=sim-from-below-Strict-Preorder}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a strict preorder" Agda=sim-from-above-Strict-Preorder}}.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a strict preorder `P`.

## Definitions

### Similarity from below of elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  sim-from-below-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  sim-from-below-Strict-Preorder x y =
    (u : type-Strict-Preorder P) →
    le-Strict-Preorder P u x ↔ le-Strict-Preorder P u y

  sim-from-below-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  sim-from-below-prop-Strict-Preorder x y =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ u → le-prop-Strict-Preorder P u x ⇔ le-prop-Strict-Preorder P u y)

  is-prop-sim-from-below-Strict-Preorder :
    (x y : type-Strict-Preorder P) →
    is-prop (sim-from-below-Strict-Preorder x y)
  is-prop-sim-from-below-Strict-Preorder x y =
    is-prop-type-Prop (sim-from-below-prop-Strict-Preorder x y)
```

### Similarity from above of elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  sim-from-above-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  sim-from-above-Strict-Preorder x y =
    (u : type-Strict-Preorder P) →
    le-Strict-Preorder P x u ↔ le-Strict-Preorder P y u

  sim-from-above-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  sim-from-above-prop-Strict-Preorder x y =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ u → le-prop-Strict-Preorder P x u ⇔ le-prop-Strict-Preorder P y u)

  is-prop-sim-from-above-Strict-Preorder :
    (x y : type-Strict-Preorder P) →
    is-prop (sim-from-above-Strict-Preorder x y)
  is-prop-sim-from-above-Strict-Preorder x y =
    is-prop-type-Prop (sim-from-above-prop-Strict-Preorder x y)
```

### Similarity of elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  sim-Strict-Preorder x y =
    ( sim-from-below-Strict-Preorder P x y) ×
    ( sim-from-above-Strict-Preorder P x y)

  sim-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  sim-prop-Strict-Preorder x y =
    ( sim-from-below-prop-Strict-Preorder P x y) ∧
    ( sim-from-above-prop-Strict-Preorder P x y)

  is-prop-sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → is-prop (sim-Strict-Preorder x y)
  is-prop-sim-Strict-Preorder x y =
    is-prop-type-Prop (sim-prop-Strict-Preorder x y)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  refl-sim-from-below-Strict-Preorder :
    is-reflexive (sim-from-below-Strict-Preorder P)
  refl-sim-from-below-Strict-Preorder x u = id-iff

  refl-sim-from-above-Strict-Preorder :
    is-reflexive (sim-from-above-Strict-Preorder P)
  refl-sim-from-above-Strict-Preorder x u = id-iff

  refl-sim-Strict-Preorder :
    is-reflexive (sim-Strict-Preorder P)
  refl-sim-Strict-Preorder x =
    ( refl-sim-from-below-Strict-Preorder x ,
      refl-sim-from-above-Strict-Preorder x)
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  transitive-sim-from-below-Strict-Preorder :
    is-transitive (sim-from-below-Strict-Preorder P)
  transitive-sim-from-below-Strict-Preorder x y z p q u = p u ∘iff q u

  transitive-sim-from-above-Strict-Preorder :
    is-transitive (sim-from-above-Strict-Preorder P)
  transitive-sim-from-above-Strict-Preorder x y z p q u = p u ∘iff q u

  transitive-sim-Strict-Preorder : is-transitive (sim-Strict-Preorder P)
  transitive-sim-Strict-Preorder x y z p q =
    ( transitive-sim-from-below-Strict-Preorder x y z (pr1 p) (pr1 q) ,
      transitive-sim-from-above-Strict-Preorder x y z (pr2 p) (pr2 q))
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  symmetric-sim-from-below-Strict-Preorder :
    is-symmetric (sim-from-below-Strict-Preorder P)
  symmetric-sim-from-below-Strict-Preorder x y p u = inv-iff (p u)

  symmetric-sim-from-above-Strict-Preorder :
    is-symmetric (sim-from-above-Strict-Preorder P)
  symmetric-sim-from-above-Strict-Preorder x y p u = inv-iff (p u)

  symmetric-sim-Strict-Preorder : is-symmetric (sim-Strict-Preorder P)
  symmetric-sim-Strict-Preorder x y p =
    ( symmetric-sim-from-below-Strict-Preorder x y (pr1 p) ,
      symmetric-sim-from-above-Strict-Preorder x y (pr2 p))
```

### Similarity defines an equivalence relation

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  sim-from-below-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  sim-from-below-equivalence-relation-Strict-Preorder =
    ( sim-from-below-prop-Strict-Preorder P ,
      refl-sim-from-below-Strict-Preorder P ,
      symmetric-sim-from-below-Strict-Preorder P ,
      transitive-sim-from-below-Strict-Preorder P)

  sim-from-above-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  sim-from-above-equivalence-relation-Strict-Preorder =
    ( sim-from-above-prop-Strict-Preorder P ,
      refl-sim-from-above-Strict-Preorder P ,
      symmetric-sim-from-above-Strict-Preorder P ,
      transitive-sim-from-above-Strict-Preorder P)

  sim-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  sim-equivalence-relation-Strict-Preorder =
    ( sim-prop-Strict-Preorder P ,
      refl-sim-Strict-Preorder P ,
      symmetric-sim-Strict-Preorder P ,
      transitive-sim-Strict-Preorder P)
```
