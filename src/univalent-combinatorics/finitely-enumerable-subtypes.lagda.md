# Finitely enumerable subtypes

```agda
module univalent-combinatorics.finitely-enumerable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cartesian-products-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.unions-subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

A [subtype](foundation.subtypes.md) `S` of a type `X` is
{{#concept "finitely enumerable" disambiguation="subtype" Agda=finitely-enumerable-subtype}}
if it is
[finitely enumerable](univalent-combinatorics.finitely-enumerable-types.md) as a
type.

## Definition

```agda
module _
  {l1 l2 : Level} {X : UU l1} (S : subtype l2 X)
  where

  finite-enumeration-subtype : UU (l1 ⊔ l2)
  finite-enumeration-subtype = finite-enumeration (type-subtype S)

  is-finitely-enumerable-prop-subtype : Prop (l1 ⊔ l2)
  is-finitely-enumerable-prop-subtype =
    is-finitely-enumerable-prop (type-subtype S)

  is-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  is-finitely-enumerable-subtype = is-finitely-enumerable (type-subtype S)

finitely-enumerable-subtype :
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
finitely-enumerable-subtype l2 X =
  type-subtype (is-finitely-enumerable-prop-subtype {l2 = l2} {X = X})

module _
  {l1 l2 : Level} {X : UU l1} (S : finitely-enumerable-subtype l2 X)
  where

  subtype-finitely-enumerable-subtype : subtype l2 X
  subtype-finitely-enumerable-subtype = pr1 S

  is-finitely-enumerable-subtype-finitely-enumerable-subtype :
    is-finitely-enumerable-subtype subtype-finitely-enumerable-subtype
  is-finitely-enumerable-subtype-finitely-enumerable-subtype = pr2 S

  type-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  type-finitely-enumerable-subtype =
    type-subtype subtype-finitely-enumerable-subtype

  finitely-enumerable-type-finitely-enumerable-subtype :
    Finitely-Enumerable-Type (l1 ⊔ l2)
  finitely-enumerable-type-finitely-enumerable-subtype =
    ( type-finitely-enumerable-subtype ,
      is-finitely-enumerable-subtype-finitely-enumerable-subtype)

  inclusion-finitely-enumerable-subtype : type-finitely-enumerable-subtype → X
  inclusion-finitely-enumerable-subtype = pr1
```

## Properties

### The image of a finitely enumerable subtype under a map is finitely enumerable

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (S : finitely-enumerable-subtype l3 X)
  where

  subtype-im-finitely-enumerable-subtype : subtype (l1 ⊔ l2 ⊔ l3) Y
  subtype-im-finitely-enumerable-subtype =
    im-subtype f (subtype-finitely-enumerable-subtype S)

  type-im-finitely-enumerable-subtype : UU (l1 ⊔ l2 ⊔ l3)
  type-im-finitely-enumerable-subtype =
    type-subtype subtype-im-finitely-enumerable-subtype

  abstract
    is-finitely-enumerable-subtype-im-finitely-enumerable-subtype :
      is-finitely-enumerable-subtype subtype-im-finitely-enumerable-subtype
    is-finitely-enumerable-subtype-im-finitely-enumerable-subtype =
      is-finitely-enumerable-im-Finitely-Enumerable-Type
        ( finitely-enumerable-type-finitely-enumerable-subtype S)
        ( f ∘ inclusion-finitely-enumerable-subtype S)

  im-finitely-enumerable-subtype :
    finitely-enumerable-subtype (l1 ⊔ l2 ⊔ l3) Y
  im-finitely-enumerable-subtype =
    ( subtype-im-finitely-enumerable-subtype ,
      is-finitely-enumerable-subtype-im-finitely-enumerable-subtype)
```

### Cartesian products of finitely enumerable subtypes

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (S@(subS , eS) : finitely-enumerable-subtype l3 X)
  (T@(subT , eT) : finitely-enumerable-subtype l4 Y)
  where

  product-finitely-enumerable-subtype :
    finitely-enumerable-subtype (l3 ⊔ l4) (X × Y)
  product-finitely-enumerable-subtype =
    ( product-subtype subS subT ,
      is-finitely-enumerable-equiv
        ( inv-equiv (equiv-product-subtype subS subT))
        ( is-finitely-enumerable-product eS eT))
```

### Finitely enumerable subtypes are closed under unions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  (S@(subS , fin-enum-S) : finitely-enumerable-subtype l2 X)
  (T@(subT , fin-enum-T) : finitely-enumerable-subtype l3 X)
  where

  subtype-union-finitely-enumerable-subtype : subtype (l2 ⊔ l3) X
  subtype-union-finitely-enumerable-subtype =
    union-subtype subS subT

  abstract
    is-finitely-enumerable-subtype-union-finitely-enumerable-subtype :
      is-finitely-enumerable-subtype subtype-union-finitely-enumerable-subtype
    is-finitely-enumerable-subtype-union-finitely-enumerable-subtype =
      is-finitely-enumerable-surjection
        ( surjection-coproduct-union-subtype subS subT)
        ( is-finitely-enumerable-coproduct fin-enum-S fin-enum-T)

  union-finitely-enumerable-subtype : finitely-enumerable-subtype (l2 ⊔ l3) X
  union-finitely-enumerable-subtype =
    ( subtype-union-finitely-enumerable-subtype ,
      is-finitely-enumerable-subtype-union-finitely-enumerable-subtype)
```

### Empty subtypes are finitely enumerable

```agda
abstract
  is-finitely-enumerable-subtype-is-empty-subtype :
    {l1 l2 : Level} {X : UU l1} (S : subtype l2 X) →
    is-empty-subtype S → is-finitely-enumerable-subtype S
  is-finitely-enumerable-subtype-is-empty-subtype S ¬S =
    is-finitely-enumerable-is-empty (is-empty-type-is-empty-subtype S ¬S)

  is-finitely-enumerable-empty-subtype :
    {l1 : Level} (l2 : Level) (X : UU l1) →
    is-finitely-enumerable-subtype (empty-subtype l2 X)
  is-finitely-enumerable-empty-subtype l2 X =
    is-finitely-enumerable-subtype-is-empty-subtype
      ( empty-subtype l2 X)
      ( is-empty-subtype-empty-subtype X)

empty-finitely-enumerable-subtype :
  {l1 : Level} (l2 : Level) (X : UU l1) → finitely-enumerable-subtype l2 X
empty-finitely-enumerable-subtype l2 X =
  ( empty-subtype l2 X ,
    is-finitely-enumerable-empty-subtype l2 X)
```

## See also

- [Inhabited finitely enumerable subtypes](univalent-combinatorics.inhabited-finitely-enumerable-subtypes.md)
