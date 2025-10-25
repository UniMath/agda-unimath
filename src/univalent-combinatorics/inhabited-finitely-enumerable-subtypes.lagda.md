# Inhabited finitely enumerable subtypes

```agda
module univalent-combinatorics.inhabited-finitely-enumerable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.images
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.inhabited-finitely-enumerable-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An
{{#concept "inhabited finitely enumerable subtype" Agda=inhabited-finitely-enumerable-subtype}}
is a [subtype](foundation.subtypes.md) that is
[inhabited](foundation.inhabited-subtypes.md) and
[finitely enumerable](univalent-combinatorics.finitely-enumerable-subtypes.md).

## Definition

```agda
inhabited-finitely-enumerable-subtype :
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
inhabited-finitely-enumerable-subtype {l1} l2 X =
  type-subtype
    ( is-inhabited-subtype-Prop {l2 = l2} ∘
      subtype-finitely-enumerable-subtype {X = X})

module _
  {l1 l2 : Level} {X : UU l1} (S : inhabited-finitely-enumerable-subtype l2 X)
  where

  finitely-enumerable-subtype-inhabited-finitely-enumerable-subtype :
    finitely-enumerable-subtype l2 X
  finitely-enumerable-subtype-inhabited-finitely-enumerable-subtype = pr1 S

  subtype-inhabited-finitely-enumerable-subtype : subtype l2 X
  subtype-inhabited-finitely-enumerable-subtype =
    subtype-finitely-enumerable-subtype
      ( finitely-enumerable-subtype-inhabited-finitely-enumerable-subtype)

  type-inhabited-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  type-inhabited-finitely-enumerable-subtype =
    type-subtype subtype-inhabited-finitely-enumerable-subtype

  is-inhabited-type-inhabited-finitely-enumerable-subtype :
    is-inhabited type-inhabited-finitely-enumerable-subtype
  is-inhabited-type-inhabited-finitely-enumerable-subtype = pr2 S

  is-finitely-enumerable-type-inhabited-finitely-enumerable-subtype :
    is-finitely-enumerable type-inhabited-finitely-enumerable-subtype
  is-finitely-enumerable-type-inhabited-finitely-enumerable-subtype =
    is-finitely-enumerable-subtype-finitely-enumerable-subtype
      ( finitely-enumerable-subtype-inhabited-finitely-enumerable-subtype)

  finitely-enumerable-type-inhabited-finitely-enumerable-subtype :
    Finitely-Enumerable-Type (l1 ⊔ l2)
  finitely-enumerable-type-inhabited-finitely-enumerable-subtype =
    finitely-enumerable-type-finitely-enumerable-subtype
      ( finitely-enumerable-subtype-inhabited-finitely-enumerable-subtype)

  inhabited-finitely-enumerable-type-inhabited-finitely-enumerable-subtype :
    Inhabited-Finitely-Enumerable-Type (l1 ⊔ l2)
  inhabited-finitely-enumerable-type-inhabited-finitely-enumerable-subtype =
    ( finitely-enumerable-type-inhabited-finitely-enumerable-subtype ,
      is-inhabited-type-inhabited-finitely-enumerable-subtype)
```

## Properties

### The image of an inhabited finitely enumerable subtype under a map is inhabited finitely enumerable

```agda
im-inhabited-finitely-enumerable-subtype :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → (X → Y) →
  inhabited-finitely-enumerable-subtype l3 X →
  inhabited-finitely-enumerable-subtype (l1 ⊔ l2 ⊔ l3) Y
im-inhabited-finitely-enumerable-subtype f (S , |S|) =
  ( im-finitely-enumerable-subtype f S ,
    map-is-inhabited
      ( map-unit-im (f ∘ inclusion-finitely-enumerable-subtype S))
      ( |S|))
```

### For an inhabited finitely enumerable subtype `S ⊆ X`, there exists `n : ℕ` such that `Fin (succ-ℕ n)` surjects onto `S`

```agda
abstract
  exists-enumeration-inhabited-finitely-enumerable-subtype :
    {l1 l2 : Level} {X : UU l1} →
    (S : inhabited-finitely-enumerable-subtype l2 X) →
    is-inhabited
      ( Σ
        ( ℕ)
        ( λ n → Fin (succ-ℕ n) ↠ type-inhabited-finitely-enumerable-subtype S))
  exists-enumeration-inhabited-finitely-enumerable-subtype S =
    exists-enumeration-Inhabited-Finitely-Enumerable-Type
      ( inhabited-finitely-enumerable-type-inhabited-finitely-enumerable-subtype
        ( S))
```
