# Finitely enumerable subtypes

```agda
module univalent-combinatorics.finitely-enumerable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
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
```
