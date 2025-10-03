# Similarity of elements in large strict preorders

```agda
module order-theory.similarity-of-elements-large-strict-preorders where
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

open import order-theory.large-strict-preorders
open import order-theory.similarity-of-elements-strict-preorders
open import order-theory.strict-preorders
```

</details>

## Idea

Two elements `x` and `y` of a
[large strict preorder](order-theory.large-strict-preorders.md) `P` are said to
be
{{#concept "similar" Disambiguation="elements of a large strict preorder" Agda=sim-Large-Strict-Preorder}},
or **indiscernible**, if for every `z : P` we have

- `z < x` [if and only if](foundation.logical-equivalences.md) `z < y`, and
- `x < z` if and only if `y < z`.

We refer to the first condition as
{{#concept "similarity from below" Disambiguation="of elements of a large strict preorder" Agda=sim-from-below-Large-Strict-Preorder}}
and the second condition as
{{#concept "similarity from above" Disambiguation="of elements of a large strict preorder" Agda=sim-from-above-Large-Strict-Preorder}}.

**Notation.** In informal writing we will use the notation `x ≍ y` to assert
that `x` and `y` are similar elements in a large strict preorder `P`. The symbol
`≍` is the unicode symbol [Equivalent To](https://codepoints.net/U+224d)
(agda-input: `\asymp`).

## Definitions

### Similarity from below of elements in large strict preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  sim-from-below-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    UU (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-Large-Strict-Preorder l x y =
    (u : type-Large-Strict-Preorder P l) →
    le-Large-Strict-Preorder P u x ↔ le-Large-Strict-Preorder P u y

  sim-from-below-level-prop-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    Prop (α l ⊔ β l l1 ⊔ β l l2)
  sim-from-below-level-prop-Large-Strict-Preorder l x y =
    Π-Prop
      ( type-Large-Strict-Preorder P l)
      ( λ u →
        le-prop-Large-Strict-Preorder P u x ⇔
        le-prop-Large-Strict-Preorder P u y)

  is-prop-sim-from-below-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    is-prop (sim-from-below-level-Large-Strict-Preorder l x y)
  is-prop-sim-from-below-level-Large-Strict-Preorder l x y =
    is-prop-type-Prop (sim-from-below-level-prop-Large-Strict-Preorder l x y)

  sim-from-below-Large-Strict-Preorder :
    {l1 l2 : Level} →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) → UUω
  sim-from-below-Large-Strict-Preorder x y =
    {l : Level} → sim-from-below-level-Large-Strict-Preorder l x y
```

### Similarity from above of elements in large strict preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  sim-from-above-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-Large-Strict-Preorder l x y =
    (u : type-Large-Strict-Preorder P l) →
    le-Large-Strict-Preorder P x u ↔ le-Large-Strict-Preorder P y u

  sim-from-above-level-prop-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l)
  sim-from-above-level-prop-Large-Strict-Preorder l x y =
    Π-Prop
      ( type-Large-Strict-Preorder P l)
      ( λ u →
        le-prop-Large-Strict-Preorder P x u ⇔
        le-prop-Large-Strict-Preorder P y u)

  is-prop-sim-from-above-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    is-prop (sim-from-above-level-Large-Strict-Preorder l x y)
  is-prop-sim-from-above-level-Large-Strict-Preorder l x y =
    is-prop-type-Prop (sim-from-above-level-prop-Large-Strict-Preorder l x y)

  sim-from-above-Large-Strict-Preorder :
    {l1 l2 : Level} →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) → UUω
  sim-from-above-Large-Strict-Preorder x y =
    {l : Level} → sim-from-above-level-Large-Strict-Preorder l x y
```

### Similarity of elements in large strict preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  sim-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    UU (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-Large-Strict-Preorder l x y =
    ( sim-from-below-level-Large-Strict-Preorder P l x y) ×
    ( sim-from-above-level-Large-Strict-Preorder P l x y)

  sim-level-prop-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    Prop (α l ⊔ β l1 l ⊔ β l2 l ⊔ β l l1 ⊔ β l l2)
  sim-level-prop-Large-Strict-Preorder l x y =
    ( sim-from-below-level-prop-Large-Strict-Preorder P l x y) ∧
    ( sim-from-above-level-prop-Large-Strict-Preorder P l x y)

  is-prop-sim-level-Large-Strict-Preorder :
    {l1 l2 : Level} (l : Level) →
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    is-prop (sim-level-Large-Strict-Preorder l x y)
  is-prop-sim-level-Large-Strict-Preorder l x y =
    is-prop-type-Prop (sim-level-prop-Large-Strict-Preorder l x y)

  record
    sim-Large-Strict-Preorder
    {l1 l2 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2)
    : UUω
    where
    field
      sim-from-below-sim-Large-Strict-Preorder :
        sim-from-below-Large-Strict-Preorder P x y
      sim-from-above-sim-Large-Strict-Preorder :
        sim-from-above-Large-Strict-Preorder P x y

open sim-Large-Strict-Preorder public
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  refl-sim-from-below-level-Large-Strict-Preorder :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-below-level-Large-Strict-Preorder P l)
  refl-sim-from-below-level-Large-Strict-Preorder l x u = id-iff

  refl-sim-from-below-Large-Strict-Preorder :
    {l1 : Level} (x : type-Large-Strict-Preorder P l1) →
    sim-from-below-Large-Strict-Preorder P x x
  refl-sim-from-below-Large-Strict-Preorder x u = id-iff

  refl-sim-from-above-level-Large-Strict-Preorder :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-above-level-Large-Strict-Preorder P l)
  refl-sim-from-above-level-Large-Strict-Preorder l x u = id-iff

  refl-sim-from-above-Large-Strict-Preorder :
    {l1 : Level} (x : type-Large-Strict-Preorder P l1) →
    sim-from-above-Large-Strict-Preorder P x x
  refl-sim-from-above-Large-Strict-Preorder x u = id-iff

  refl-sim-level-Large-Strict-Preorder :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-level-Large-Strict-Preorder P l)
  refl-sim-level-Large-Strict-Preorder l x =
    ( refl-sim-from-below-level-Large-Strict-Preorder l x ,
      refl-sim-from-above-level-Large-Strict-Preorder l x)

  refl-sim-Large-Strict-Preorder :
    {l1 : Level} (x : type-Large-Strict-Preorder P l1) →
    sim-Large-Strict-Preorder P x x
  refl-sim-Large-Strict-Preorder x =
    λ where
    .sim-from-below-sim-Large-Strict-Preorder →
      refl-sim-from-below-Large-Strict-Preorder x
    .sim-from-above-sim-Large-Strict-Preorder →
      refl-sim-from-above-Large-Strict-Preorder x
```

### The similarity relation is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  transitive-sim-from-below-level-Large-Strict-Preorder :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-below-level-Large-Strict-Preorder P l)
  transitive-sim-from-below-level-Large-Strict-Preorder l x y z p q u =
    p u ∘iff q u

  transitive-sim-from-below-Large-Strict-Preorder :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2)
    (z : type-Large-Strict-Preorder P l3) →
    sim-from-below-Large-Strict-Preorder P y z →
    sim-from-below-Large-Strict-Preorder P x y →
    sim-from-below-Large-Strict-Preorder P x z
  transitive-sim-from-below-Large-Strict-Preorder x y z p q u =
    p u ∘iff q u

  transitive-sim-from-above-level-Large-Strict-Preorder :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-above-level-Large-Strict-Preorder P l)
  transitive-sim-from-above-level-Large-Strict-Preorder l x y z p q u =
    p u ∘iff q u

  transitive-sim-from-above-Large-Strict-Preorder :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2)
    (z : type-Large-Strict-Preorder P l3) →
    sim-from-above-Large-Strict-Preorder P y z →
    sim-from-above-Large-Strict-Preorder P x y →
    sim-from-above-Large-Strict-Preorder P x z
  transitive-sim-from-above-Large-Strict-Preorder x y z p q u =
    p u ∘iff q u

  transitive-sim-level-Large-Strict-Preorder :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-level-Large-Strict-Preorder P l)
  transitive-sim-level-Large-Strict-Preorder l x y z p q =
    ( transitive-sim-from-below-level-Large-Strict-Preorder
        l x y z (pr1 p) (pr1 q) ,
      transitive-sim-from-above-level-Large-Strict-Preorder
        l x y z (pr2 p) (pr2 q))

  transitive-sim-Large-Strict-Preorder :
    {l1 l2 l3 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2)
    (z : type-Large-Strict-Preorder P l3) →
    sim-Large-Strict-Preorder P y z →
    sim-Large-Strict-Preorder P x y →
    sim-Large-Strict-Preorder P x z
  transitive-sim-Large-Strict-Preorder x y z p q =
    λ where
    .sim-from-below-sim-Large-Strict-Preorder →
      transitive-sim-from-below-Large-Strict-Preorder x y z
        ( sim-from-below-sim-Large-Strict-Preorder p)
        ( sim-from-below-sim-Large-Strict-Preorder q)
    .sim-from-above-sim-Large-Strict-Preorder →
      transitive-sim-from-above-Large-Strict-Preorder x y z
        ( sim-from-above-sim-Large-Strict-Preorder p)
        ( sim-from-above-sim-Large-Strict-Preorder q)
```

### The similarity relation is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  symmetric-sim-from-below-level-Large-Strict-Preorder :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-below-level-Large-Strict-Preorder P l)
  symmetric-sim-from-below-level-Large-Strict-Preorder l x y p u =
    inv-iff (p u)

  symmetric-sim-from-below-Large-Strict-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    sim-from-below-Large-Strict-Preorder P x y →
    sim-from-below-Large-Strict-Preorder P y x
  symmetric-sim-from-below-Large-Strict-Preorder x y p u =
    inv-iff (p u)

  symmetric-sim-from-above-level-Large-Strict-Preorder :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-from-above-level-Large-Strict-Preorder P l)
  symmetric-sim-from-above-level-Large-Strict-Preorder l x y p u =
    inv-iff (p u)

  symmetric-sim-from-above-Large-Strict-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    sim-from-above-Large-Strict-Preorder P x y →
    sim-from-above-Large-Strict-Preorder P y x
  symmetric-sim-from-above-Large-Strict-Preorder x y p u =
    inv-iff (p u)

  symmetric-sim-level-Large-Strict-Preorder :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Preorder P)
      ( sim-level-Large-Strict-Preorder P l)
  symmetric-sim-level-Large-Strict-Preorder l x y p =
    ( symmetric-sim-from-below-level-Large-Strict-Preorder l x y (pr1 p) ,
      symmetric-sim-from-above-level-Large-Strict-Preorder l x y (pr2 p))

  symmetric-sim-Large-Strict-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Strict-Preorder P l1)
    (y : type-Large-Strict-Preorder P l2) →
    sim-Large-Strict-Preorder P x y →
    sim-Large-Strict-Preorder P y x
  symmetric-sim-Large-Strict-Preorder x y p =
    λ where
    .sim-from-below-sim-Large-Strict-Preorder →
      symmetric-sim-from-below-Large-Strict-Preorder x y
        ( sim-from-below-sim-Large-Strict-Preorder p)
    .sim-from-above-sim-Large-Strict-Preorder →
      symmetric-sim-from-above-Large-Strict-Preorder x y
        ( sim-from-above-sim-Large-Strict-Preorder p)
```
