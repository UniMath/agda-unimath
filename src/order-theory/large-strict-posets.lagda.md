# Large strict posets

```agda
module order-theory.large-strict-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-strict-preorders
open import order-theory.similarity-of-elements-large-strict-preorders
open import order-theory.strict-posets
open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

A {{#concept "large strict poset" Agda=Large-Strict-Poset}} is a
[large strict preorder](order-theory.large-strict-preorders.md) $A$ satisfying
the
{{#concept "extensionality principle" Disambiguation="of large strict posets" Agda=extensionality-principle-Large-Strict-Preorder}}
that
[similar elements](order-theory.similarity-of-elements-large-strict-preorders.md)
are [equal](foundation-core.identity-types.md). More concretely, if $x$ and $y$
are such that for every $z$, we have

- $z < x$ [if and only if](foundation.logical-equivalences.md) $z < y$, and
- $x < z$ if and only if $y < z$,

then $x = y$.

The extensionality principle of large strict posets is slightly different to
that of [ordinals](order-theory.ordinals.md). For ordinals, elements are equal
already if they are _similar from below_. Namely, only the first of the two
conditions above must be satisfied in order for two elements to be equal.

The extensionality principle of large strict posets can be recovered as a
special case of the extensionality principle of
[semicategories](category-theory.nonunital-precategories.md) as considered in
Example 8.16 of _The Univalence Principle_ {{#cite ANST25}}.

## Definitions

### The extensionality principle of large strict posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Preorder α β)
  where

  extensionality-principle-level-Large-Strict-Preorder :
    (l : Level) → UU (α l ⊔ β l l)
  extensionality-principle-level-Large-Strict-Preorder l =
    (x y : type-Large-Strict-Preorder A l) →
    sim-level-Large-Strict-Preorder A l x y →
    x ＝ y

  extensionality-principle-Large-Strict-Preorder : UUω
  extensionality-principle-Large-Strict-Preorder =
    {l : Level} → extensionality-principle-level-Large-Strict-Preorder l

  weak-extensionality-principle-level-Large-Strict-Preorder : Level → UUω
  weak-extensionality-principle-level-Large-Strict-Preorder l =
    (x y : type-Large-Strict-Preorder A l) →
    sim-Large-Strict-Preorder A x y →
    x ＝ y

  weak-extensionality-principle-Large-Strict-Preorder : UUω
  weak-extensionality-principle-Large-Strict-Preorder =
    {l : Level} → weak-extensionality-principle-level-Large-Strict-Preorder l
```

The last, "weak", extensionality principle is in general weaker than the
extensionality principle. For instance, it is no longer the case for "weakly
extensional" large strict preorders that the underlying strict preorder at a
universe level is extensional.

### The type of large strict posets

```agda
record Large-Strict-Poset (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  field
    large-strict-preorder-Large-Strict-Poset : Large-Strict-Preorder α β

    extensionality-Large-Strict-Poset :
      extensionality-principle-Large-Strict-Preorder
        large-strict-preorder-Large-Strict-Poset

  type-Large-Strict-Poset : (l : Level) → UU (α l)
  type-Large-Strict-Poset =
    type-Large-Strict-Preorder large-strict-preorder-Large-Strict-Poset

  le-Large-Strict-Poset :
    Large-Relation β type-Large-Strict-Poset
  le-Large-Strict-Poset =
    le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Poset

  is-prop-le-Large-Strict-Poset :
    {l1 l2 : Level}
    (x : type-Large-Strict-Poset l1)
    (y : type-Large-Strict-Poset l2) →
    is-prop (le-Large-Strict-Poset x y)
  is-prop-le-Large-Strict-Poset =
    is-prop-le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Poset

  le-prop-Large-Strict-Poset : Large-Relation-Prop β type-Large-Strict-Poset
  le-prop-Large-Strict-Poset =
    le-prop-Large-Strict-Preorder large-strict-preorder-Large-Strict-Poset

  is-irreflexive-le-Large-Strict-Poset :
    is-antireflexive-Large-Relation
      type-Large-Strict-Poset
      le-Large-Strict-Poset
  is-irreflexive-le-Large-Strict-Poset =
    is-irreflexive-le-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  is-transitive-le-Large-Strict-Poset :
    is-transitive-Large-Relation type-Large-Strict-Poset le-Large-Strict-Poset
  is-transitive-le-Large-Strict-Poset =
    transitive-le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Poset
```

Similarity of elements in large strict posets.

```agda
  sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    Large-Relation (λ l1 l2 → α l ⊔ β l l1 ⊔ β l l2) type-Large-Strict-Poset
  sim-from-below-level-Large-Strict-Poset l =
    sim-from-below-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  is-prop-sim-from-below-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset l1)
    (y : type-Large-Strict-Poset l2) →
    is-prop (sim-from-below-level-Large-Strict-Poset l x y)
  is-prop-sim-from-below-level-Large-Strict-Poset l =
    is-prop-sim-from-below-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  sim-from-below-level-prop-Large-Strict-Poset :
    (l : Level) →
    Large-Relation-Prop
      ( λ l1 l2 → α l ⊔ β l l1 ⊔ β l l2)
      ( type-Large-Strict-Poset)
  sim-from-below-level-prop-Large-Strict-Poset l =
    sim-from-below-level-prop-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  refl-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-below-level-Large-Strict-Poset l)
  refl-sim-from-below-level-Large-Strict-Poset =
    refl-sim-from-below-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  symmetric-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-below-level-Large-Strict-Poset l)
  symmetric-sim-from-below-level-Large-Strict-Poset =
    symmetric-sim-from-below-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  transitive-sim-from-below-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-below-level-Large-Strict-Poset l)
  transitive-sim-from-below-level-Large-Strict-Poset =
    transitive-sim-from-below-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    Large-Relation (λ l1 l2 → α l ⊔ β l1 l ⊔ β l2 l) type-Large-Strict-Poset
  sim-from-above-level-Large-Strict-Poset l =
    sim-from-above-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  is-prop-sim-from-above-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset l1)
    (y : type-Large-Strict-Poset l2) →
    is-prop (sim-from-above-level-Large-Strict-Poset l x y)
  is-prop-sim-from-above-level-Large-Strict-Poset l =
    is-prop-sim-from-above-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  sim-from-above-level-prop-Large-Strict-Poset :
    (l : Level) →
    Large-Relation-Prop
      ( λ l1 l2 → α l ⊔ β l1 l ⊔ β l2 l)
      ( type-Large-Strict-Poset)
  sim-from-above-level-prop-Large-Strict-Poset l =
    sim-from-above-level-prop-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  refl-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-above-level-Large-Strict-Poset l)
  refl-sim-from-above-level-Large-Strict-Poset =
    refl-sim-from-above-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  symmetric-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-above-level-Large-Strict-Poset l)
  symmetric-sim-from-above-level-Large-Strict-Poset =
    symmetric-sim-from-above-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  transitive-sim-from-above-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-from-above-level-Large-Strict-Poset l)
  transitive-sim-from-above-level-Large-Strict-Poset =
    transitive-sim-from-above-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  sim-level-Large-Strict-Poset :
    (l : Level) →
    Large-Relation
      ( λ l1 l2 → α l ⊔ β l l1 ⊔ β l l2 ⊔ β l1 l ⊔ β l2 l)
      ( type-Large-Strict-Poset)
  sim-level-Large-Strict-Poset l =
    sim-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  is-prop-sim-level-Large-Strict-Poset :
    {l1 l2 : Level} (l : Level)
    (x : type-Large-Strict-Poset l1)
    (y : type-Large-Strict-Poset l2) →
    is-prop (sim-level-Large-Strict-Poset l x y)
  is-prop-sim-level-Large-Strict-Poset l =
    is-prop-sim-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  sim-level-prop-Large-Strict-Poset :
    (l : Level) →
    Large-Relation-Prop
      ( λ l1 l2 → α l ⊔ β l l1 ⊔ β l l2 ⊔ β l1 l ⊔ β l2 l)
      ( type-Large-Strict-Poset)
  sim-level-prop-Large-Strict-Poset l =
    sim-level-prop-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset l

  refl-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-reflexive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-level-Large-Strict-Poset l)
  refl-sim-level-Large-Strict-Poset =
    refl-sim-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  symmetric-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-symmetric-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-level-Large-Strict-Poset l)
  symmetric-sim-level-Large-Strict-Poset =
    symmetric-sim-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

  transitive-sim-level-Large-Strict-Poset :
    (l : Level) →
    is-transitive-Large-Relation
      ( type-Large-Strict-Poset)
      ( sim-level-Large-Strict-Poset l)
  transitive-sim-level-Large-Strict-Poset =
    transitive-sim-level-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Poset

open Large-Strict-Poset public
```

## Properties

### The underlying strict poset at a universe level

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Poset α β)
  where

  strict-preorder-Large-Strict-Poset :
    (l : Level) → Strict-Preorder (α l) (β l l)
  strict-preorder-Large-Strict-Poset =
    strict-preorder-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Poset A)

  extensionality-strict-preorder-Large-Strict-Poset :
    (l : Level) →
    extensionality-principle-Strict-Preorder
      ( strict-preorder-Large-Strict-Poset l)
  extensionality-strict-preorder-Large-Strict-Poset l =
    extensionality-Large-Strict-Poset A

  strict-poset-Large-Strict-Poset :
    (l : Level) → Strict-Poset (α l) (β l l)
  strict-poset-Large-Strict-Poset l =
    ( strict-preorder-Large-Strict-Poset l ,
      extensionality-strict-preorder-Large-Strict-Poset l)
```

## References

{{#bibliography}}
