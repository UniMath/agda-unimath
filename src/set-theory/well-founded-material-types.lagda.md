# Well-founded material types

```agda
module set-theory.well-founded-material-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.separated-types-subuniverses
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.torsorial-type-families

open import order-theory.accessible-elements-relations
open import order-theory.preorders
open import order-theory.well-founded-relations

open import orthogonal-factorization-systems.reflective-global-subuniverses

open import set-theory.elementhood-structures
open import set-theory.material-types
```

</details>

## Idea

A [material type](set-theory.material-types.md) `A` is
{{#concept "well-founded" Disambiguation="material type" Agda=is-well-founded-Material-Type Agda=Well-Founded-Material-Type}}
if its underlying [elementhood relation](set-theory.elementhood-structures.md)
`∈` satisfies the [property](foundation-core.propositions.md) of being
[well-founded](order-theory.well-founded-relations.md).

Well-founded material types satisfy an induction principle: given a type family
`P : A → Type` then in order to construct an element of `P x` for all `x : A` it
suffices to construct an element of `P u` for all elements `u ∈ x`. More
precisely, the
{{#concept "well-founded induction principle" WDID=Q14402036 WD="well-founded induction" Agda=ind-Well-Founded-Material-Type}}
is a function

```text
  (x : X) → ((u : A) → (u ∈ x) → P u) → P x.
```

In {{#cite GS24}}, such types are said to have elementhood structures that
satisfy _foundation_.

## Definitions

### The predicate on a material type of being well-founded

```agda
module _
  {l1 l2 : Level} (A : Material-Type l1 l2)
  (let _∈_ = elementhood-Material-Type A)
  where

  is-well-founded-Material-Type : UU (l1 ⊔ l2)
  is-well-founded-Material-Type =
    is-well-founded-Relation _∈_

  is-well-founded-prop-Material-Type : Prop (l1 ⊔ l2)
  is-well-founded-prop-Material-Type =
    is-well-founded-prop-Relation _∈_

  is-prop-is-well-founded-Material-Type :
    is-prop is-well-founded-Material-Type
  is-prop-is-well-founded-Material-Type =
    is-prop-is-well-founded-Relation _∈_
```

### The type of well-founded material types

```agda
Well-Founded-Material-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Well-Founded-Material-Type l1 l2 =
  Σ (Material-Type l1 l2) is-well-founded-Material-Type

module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  where

  material-type-Well-Founded-Material-Type : Material-Type l1 l2
  material-type-Well-Founded-Material-Type = pr1 A

  is-well-founded-Well-Founded-Material-Type :
    is-well-founded-Material-Type material-type-Well-Founded-Material-Type
  is-well-founded-Well-Founded-Material-Type = pr2 A

  type-Well-Founded-Material-Type : UU l1
  type-Well-Founded-Material-Type =
    type-Material-Type material-type-Well-Founded-Material-Type

  elementhood-structure-Well-Founded-Material-Type :
    Elementhood-Structure l2 type-Well-Founded-Material-Type
  elementhood-structure-Well-Founded-Material-Type =
    elementhood-structure-Material-Type
      ( material-type-Well-Founded-Material-Type)

  elementhood-Well-Founded-Material-Type :
    Relation l2 type-Well-Founded-Material-Type
  elementhood-Well-Founded-Material-Type =
    elementhood-Material-Type
      ( material-type-Well-Founded-Material-Type)

  is-extensional-elementhood-structure-Well-Founded-Material-Type :
    is-extensional-elementhood-Relation elementhood-Well-Founded-Material-Type
  is-extensional-elementhood-structure-Well-Founded-Material-Type =
    is-extensional-elementhood-structure-Material-Type
      ( material-type-Well-Founded-Material-Type)

  well-founded-relation-Well-Founded-Material-Type :
    Well-Founded-Relation l2 type-Well-Founded-Material-Type
  well-founded-relation-Well-Founded-Material-Type =
    ( elementhood-Well-Founded-Material-Type ,
      is-well-founded-Well-Founded-Material-Type)

module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  (let _∈_ = elementhood-Well-Founded-Material-Type A)
  where

  equiv-elementhood-eq-Well-Founded-Material-Type :
    (x y : type-Well-Founded-Material-Type A) →
    (x ＝ y) → (u : type-Well-Founded-Material-Type A) → (u ∈ x) ≃ (u ∈ y)
  equiv-elementhood-eq-Well-Founded-Material-Type =
    equiv-elementhood-eq-Material-Type
      ( material-type-Well-Founded-Material-Type A)

  extensionality-Well-Founded-Material-Type :
    (x y : type-Well-Founded-Material-Type A) →
    (x ＝ y) ≃ ((u : type-Well-Founded-Material-Type A) → (u ∈ x) ≃ (u ∈ y))
  extensionality-Well-Founded-Material-Type =
    extensionality-Material-Type
      ( material-type-Well-Founded-Material-Type A)

  inv-extensionality-Well-Founded-Material-Type :
    (x y : type-Well-Founded-Material-Type A) →
    ((u : type-Well-Founded-Material-Type A) → (u ∈ x) ≃ (u ∈ y)) ≃ (x ＝ y)
  inv-extensionality-Well-Founded-Material-Type =
    inv-extensionality-Material-Type
      ( material-type-Well-Founded-Material-Type A)

  eq-equiv-elementhood-Well-Founded-Material-Type :
    (x y : type-Well-Founded-Material-Type A) →
    ((u : type-Well-Founded-Material-Type A) → (u ∈ x) ≃ (u ∈ y)) → (x ＝ y)
  eq-equiv-elementhood-Well-Founded-Material-Type =
    eq-equiv-elementhood-Material-Type
      ( material-type-Well-Founded-Material-Type A)
```

### Well-founded induction

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  (let A' = type-Well-Founded-Material-Type A)
  (let _∈_ = elementhood-Well-Founded-Material-Type A)
  where

  ind-Well-Founded-Material-Type :
    {l3 : Level} (P : A' → UU l3) →
    ({x : A'} → ({u : A'} → u ∈ x → P u) → P x) → (x : A') → P x
  ind-Well-Founded-Material-Type =
    ind-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Type A)
```

### The type of elements of an element

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  where

  element-Well-Founded-Material-Type :
    type-Well-Founded-Material-Type A → UU (l1 ⊔ l2)
  element-Well-Founded-Material-Type =
    element-Material-Type (material-type-Well-Founded-Material-Type A)
```

## Properties

### Uniqueness of comprehensions

This is Proposition 4 of {{#cite GS24}}.

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  (let _∈_ = elementhood-Well-Founded-Material-Type A)
  where

  uniqueness-comprehension-Well-Founded-Material-Type' :
    {l3 : Level} (ϕ : type-Well-Founded-Material-Type A → UU l3) →
    is-proof-irrelevant
      ( Σ ( type-Well-Founded-Material-Type A)
          ( λ x → (u : type-Well-Founded-Material-Type A) → ϕ u ≃ (u ∈ x)))
  uniqueness-comprehension-Well-Founded-Material-Type' =
    uniqueness-comprehension-Material-Type'
      ( material-type-Well-Founded-Material-Type A)

  uniqueness-comprehension-Well-Founded-Material-Type :
    {l3 : Level} (ϕ : type-Well-Founded-Material-Type A → UU l3) →
    is-prop
      ( Σ ( type-Well-Founded-Material-Type A)
          ( λ x → (u : type-Well-Founded-Material-Type A) → ϕ u ≃ (u ∈ x)))
  uniqueness-comprehension-Well-Founded-Material-Type =
    uniqueness-comprehension-Material-Type
      ( material-type-Well-Founded-Material-Type A)
```

## Properties

### Well-founded elementhood relations are asymmetric

```agda
module _
  {l1 l2 : Level} (A : Well-Founded-Material-Type l1 l2)
  (let _∈_ = elementhood-Well-Founded-Material-Type A)
  where

  asymmetric-elementhood-Well-Founded-Material-Type : is-asymmetric _∈_
  asymmetric-elementhood-Well-Founded-Material-Type =
    is-asymmetric-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Type A)

  irreflexive-elementhood-Well-Founded-Material-Type : is-irreflexive _∈_
  irreflexive-elementhood-Well-Founded-Material-Type =
    is-irreflexive-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Material-Type A)
```

## References

{{#bibliography}}

## External links

- <https://elisabeth.stenholm.one/univalent-material-set-theory/e-structure.property.foundation.html>
