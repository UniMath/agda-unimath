# Well-founded material sets

```agda
module set-theory.well-founded-material-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.well-founded-relations

open import set-theory.elementhood-structures
open import set-theory.material-sets
```

</details>

## Idea

A [material set](set-theory.material-sets.md) `A` is
{{#concept "well-founded" Disambiguation="material set" Agda=is-well-founded-Material-Set Agda=Well-Founded-Material-Set}}
if its underlying [elementhood relation](set-theory.elementhood-structures.md)
`∈` satisfies the [property](foundation-core.propositions.md) of being
[well-founded](order-theory.well-founded-relations.md).

Well-founded material sets satisfy an induction principle: given a type family
`P : A → Type` then in order to construct an element of `P x` for all `x : A` it
suffices to construct an element of `P u` for all elements `u ∈ x`. More
precisely, the
{{#concept "well-founded induction principle" Disambiguation="of a well-founded material set" WDID=Q14402036 WD="well-founded induction" Agda=ind-Well-Founded-Material-Set}}
is a function

```text
  (x : X) → ((u : A) → (u ∈ x) → P u) → P x.
```

In {{#cite GS26}}, such types are said to have elementhood structures that
satisfy _foundation_.

## Definitions

### The predicate on a material set of being well-founded

```agda
module _
  {l1 l2 : Level} (A : Material-Set l1 l2)
  (let _∈_ = elementhood-Material-Set A)
  where

  is-well-founded-Material-Set : UU (l1 ⊔ l2)
  is-well-founded-Material-Set =
    is-well-founded-Relation _∈_

  is-well-founded-prop-Material-Set : Prop (l1 ⊔ l2)
  is-well-founded-prop-Material-Set =
    is-well-founded-prop-Relation _∈_

  is-prop-is-well-founded-Material-Set :
    is-prop is-well-founded-Material-Set
  is-prop-is-well-founded-Material-Set =
    is-prop-is-well-founded-Relation _∈_
```

### The type of well-founded material sets

```agda
Well-Founded-Material-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Well-Founded-Material-Set l1 l2 =
  Σ (Material-Set l1 l2) is-well-founded-Material-Set

module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  where

  material-set-Well-Founded-Material-Set : Material-Set l1 l2
  material-set-Well-Founded-Material-Set = pr1 A

  is-well-founded-Well-Founded-Material-Set :
    is-well-founded-Material-Set material-set-Well-Founded-Material-Set
  is-well-founded-Well-Founded-Material-Set = pr2 A

  type-Well-Founded-Material-Set : UU l1
  type-Well-Founded-Material-Set =
    type-Material-Set material-set-Well-Founded-Material-Set

  elementhood-structure-Well-Founded-Material-Set :
    Elementhood-Structure l2 type-Well-Founded-Material-Set
  elementhood-structure-Well-Founded-Material-Set =
    elementhood-structure-Material-Set
      ( material-set-Well-Founded-Material-Set)

  elementhood-Well-Founded-Material-Set :
    Relation l2 type-Well-Founded-Material-Set
  elementhood-Well-Founded-Material-Set =
    elementhood-Material-Set
      ( material-set-Well-Founded-Material-Set)

  is-extensional-elementhood-structure-Well-Founded-Material-Set :
    is-extensional-elementhood-Relation elementhood-Well-Founded-Material-Set
  is-extensional-elementhood-structure-Well-Founded-Material-Set =
    is-extensional-elementhood-structure-Material-Set
      ( material-set-Well-Founded-Material-Set)

  well-founded-relation-Well-Founded-Material-Set :
    Well-Founded-Relation l2 type-Well-Founded-Material-Set
  well-founded-relation-Well-Founded-Material-Set =
    ( elementhood-Well-Founded-Material-Set ,
      is-well-founded-Well-Founded-Material-Set)

module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  (let A' = type-Well-Founded-Material-Set A)
  (let _∈_ = elementhood-Well-Founded-Material-Set A)
  where

  equiv-elementhood-eq-Well-Founded-Material-Set :
    {x y : A'} → (x ＝ y) → (u : A') → (u ∈ x) ≃ (u ∈ y)
  equiv-elementhood-eq-Well-Founded-Material-Set =
    equiv-elementhood-eq-Material-Set
      ( material-set-Well-Founded-Material-Set A)

  extensionality-Well-Founded-Material-Set :
    (x y : A') → (x ＝ y) ≃ ((u : A') → (u ∈ x) ≃ (u ∈ y))
  extensionality-Well-Founded-Material-Set =
    extensionality-Material-Set
      ( material-set-Well-Founded-Material-Set A)

  inv-extensionality-Well-Founded-Material-Set :
    (x y : A') → ((u : A') → (u ∈ x) ≃ (u ∈ y)) ≃ (x ＝ y)
  inv-extensionality-Well-Founded-Material-Set =
    inv-extensionality-Material-Set
      ( material-set-Well-Founded-Material-Set A)

  eq-equiv-elementhood-Well-Founded-Material-Set :
    {x y : A'} → ((u : A') → (u ∈ x) ≃ (u ∈ y)) → (x ＝ y)
  eq-equiv-elementhood-Well-Founded-Material-Set =
    eq-equiv-elementhood-Material-Set
      ( material-set-Well-Founded-Material-Set A)
```

### Well-founded induction

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  (let A' = type-Well-Founded-Material-Set A)
  (let _∈_ = elementhood-Well-Founded-Material-Set A)
  where

  ind-Well-Founded-Material-Set :
    {l3 : Level} (P : A' → UU l3) →
    ({x : A'} → ({u : A'} → u ∈ x → P u) → P x) → (x : A') → P x
  ind-Well-Founded-Material-Set =
    ind-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Set A)
```

### The type of elements of an element

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  where

  element-Well-Founded-Material-Set :
    type-Well-Founded-Material-Set A → UU (l1 ⊔ l2)
  element-Well-Founded-Material-Set =
    element-Material-Set (material-set-Well-Founded-Material-Set A)
```

## Properties

### Uniqueness of comprehensions

This is Proposition 4 of {{#cite GS26}}.

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  (let A' = type-Well-Founded-Material-Set A)
  (let _∈_ = elementhood-Well-Founded-Material-Set A)
  where

  uniqueness-comprehension-Well-Founded-Material-Set' :
    {l3 : Level} (ϕ : A' → UU l3) →
    is-proof-irrelevant (Σ A' (λ x → (u : A') → ϕ u ≃ (u ∈ x)))
  uniqueness-comprehension-Well-Founded-Material-Set' =
    uniqueness-comprehension-Material-Set'
      ( material-set-Well-Founded-Material-Set A)

  uniqueness-comprehension-Well-Founded-Material-Set :
    {l3 : Level} (ϕ : A' → UU l3) →
    is-prop (Σ A' (λ x → (u : A') → ϕ u ≃ (u ∈ x)))
  uniqueness-comprehension-Well-Founded-Material-Set =
    uniqueness-comprehension-Material-Set
      ( material-set-Well-Founded-Material-Set A)
```

## Properties

### Well-founded elementhood relations are asymmetric

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  (let _∈_ = elementhood-Well-Founded-Material-Set A)
  where

  asymmetric-elementhood-Well-Founded-Material-Set : is-asymmetric _∈_
  asymmetric-elementhood-Well-Founded-Material-Set =
    is-asymmetric-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Set A)
```

### Well-founded elementhood relations are irreflexive

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Set l1 l2)
  (let _∈_ = elementhood-Well-Founded-Material-Set A)
  where

  irreflexive-elementhood-Well-Founded-Material-Set : is-irreflexive _∈_
  irreflexive-elementhood-Well-Founded-Material-Set =
    is-irreflexive-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Set A)
```

## References

{{#bibliography}}

## External links

- <https://elisabeth.stenholm.one/univalent-material-set-theory/e-structure.property.foundation.html>
