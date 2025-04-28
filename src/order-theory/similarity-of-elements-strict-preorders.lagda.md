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
{{#concept "lower similarity" Disambiguation="of elements of a strict preorder" Agda=lower-sim-Strict-Preorder}}
and the second condition as
{{#concept "upper similarity" Disambiguation="of elements of a strict preorder" Agda=upper-sim-Strict-Preorder}}.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a strict preorder `P`.

## Definitions

### Lower similar elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  lower-sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  lower-sim-Strict-Preorder x y =
    (u : type-Strict-Preorder P) →
    le-Strict-Preorder P u x ↔ le-Strict-Preorder P u y

  lower-sim-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  lower-sim-prop-Strict-Preorder x y =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ u → le-prop-Strict-Preorder P u x ⇔ le-prop-Strict-Preorder P u y)

  is-prop-lower-sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → is-prop (lower-sim-Strict-Preorder x y)
  is-prop-lower-sim-Strict-Preorder x y =
    is-prop-type-Prop (lower-sim-prop-Strict-Preorder x y)
```

### Upper similar elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  upper-sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  upper-sim-Strict-Preorder x y =
    (u : type-Strict-Preorder P) →
    le-Strict-Preorder P x u ↔ le-Strict-Preorder P y u

  upper-sim-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  upper-sim-prop-Strict-Preorder x y =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ u → le-prop-Strict-Preorder P x u ⇔ le-prop-Strict-Preorder P y u)

  is-prop-upper-sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → is-prop (upper-sim-Strict-Preorder x y)
  is-prop-upper-sim-Strict-Preorder x y =
    is-prop-type-Prop (upper-sim-prop-Strict-Preorder x y)
```

### Similar elements in strict preorders

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  sim-Strict-Preorder :
    (x y : type-Strict-Preorder P) → UU (l1 ⊔ l2)
  sim-Strict-Preorder x y =
    (lower-sim-Strict-Preorder P x y) × (upper-sim-Strict-Preorder P x y)

  sim-prop-Strict-Preorder :
    (x y : type-Strict-Preorder P) → Prop (l1 ⊔ l2)
  sim-prop-Strict-Preorder x y =
    ( lower-sim-prop-Strict-Preorder P x y) ∧
    ( upper-sim-prop-Strict-Preorder P x y)

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

  refl-lower-sim-Strict-Preorder : is-reflexive (lower-sim-Strict-Preorder P)
  refl-lower-sim-Strict-Preorder x u = id-iff

  refl-upper-sim-Strict-Preorder : is-reflexive (upper-sim-Strict-Preorder P)
  refl-upper-sim-Strict-Preorder x u = id-iff

  refl-sim-Strict-Preorder : is-reflexive (sim-Strict-Preorder P)
  refl-sim-Strict-Preorder x =
    ( refl-lower-sim-Strict-Preorder x , refl-upper-sim-Strict-Preorder x)
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  transitive-lower-sim-Strict-Preorder :
    is-transitive (lower-sim-Strict-Preorder P)
  transitive-lower-sim-Strict-Preorder x y z p q u = p u ∘iff q u

  transitive-upper-sim-Strict-Preorder :
    is-transitive (upper-sim-Strict-Preorder P)
  transitive-upper-sim-Strict-Preorder x y z p q u = p u ∘iff q u

  transitive-sim-Strict-Preorder : is-transitive (sim-Strict-Preorder P)
  transitive-sim-Strict-Preorder x y z p q =
    ( transitive-lower-sim-Strict-Preorder x y z (pr1 p) (pr1 q) ,
      transitive-upper-sim-Strict-Preorder x y z (pr2 p) (pr2 q))
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  symmetric-lower-sim-Strict-Preorder :
    is-symmetric (lower-sim-Strict-Preorder P)
  symmetric-lower-sim-Strict-Preorder x y p u = inv-iff (p u)

  symmetric-upper-sim-Strict-Preorder :
    is-symmetric (upper-sim-Strict-Preorder P)
  symmetric-upper-sim-Strict-Preorder x y p u = inv-iff (p u)

  symmetric-sim-Strict-Preorder : is-symmetric (sim-Strict-Preorder P)
  symmetric-sim-Strict-Preorder x y p =
    ( symmetric-lower-sim-Strict-Preorder x y (pr1 p) ,
      symmetric-upper-sim-Strict-Preorder x y (pr2 p))
```

### Similarity defines an equivalence relation

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  lower-sim-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  lower-sim-equivalence-relation-Strict-Preorder =
    ( lower-sim-prop-Strict-Preorder P ,
      refl-lower-sim-Strict-Preorder P ,
      symmetric-lower-sim-Strict-Preorder P ,
      transitive-lower-sim-Strict-Preorder P)

  upper-sim-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  upper-sim-equivalence-relation-Strict-Preorder =
    ( upper-sim-prop-Strict-Preorder P ,
      refl-upper-sim-Strict-Preorder P ,
      symmetric-upper-sim-Strict-Preorder P ,
      transitive-upper-sim-Strict-Preorder P)

  sim-equivalence-relation-Strict-Preorder :
    equivalence-relation (l1 ⊔ l2) (type-Strict-Preorder P)
  sim-equivalence-relation-Strict-Preorder =
    ( sim-prop-Strict-Preorder P ,
      refl-sim-Strict-Preorder P ,
      symmetric-sim-Strict-Preorder P ,
      transitive-sim-Strict-Preorder P)
```
