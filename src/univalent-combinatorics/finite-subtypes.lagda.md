# Finite subtypes

```agda
module univalent-combinatorics.finite-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A [subtype](foundation.subtypes.md) is
{{#concept "finite" Disambiguation="subtype" Agda=is-finite WD="finite set" WDID=Q272404 Agda=is-finite-subtype}}
if its type is [finite](univalent-combinatorics.finite-types.md).

## Definition

```agda
is-finite-prop-subtype :
  {l1 l2 : Level} {X : UU l1} → subtype l2 X → Prop (l1 ⊔ l2)
is-finite-prop-subtype S = is-finite-Prop (type-subtype S)

is-finite-subtype :
  {l1 l2 : Level} {X : UU l1} → subtype l2 X → UU (l1 ⊔ l2)
is-finite-subtype S = type-Prop (is-finite-prop-subtype S)

finite-subtype : {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
finite-subtype l2 X = type-subtype (is-finite-prop-subtype {l2 = l2} {X = X})

module _
  {l1 l2 : Level} {X : UU l1} (S : finite-subtype l2 X)
  where

  subtype-finite-subtype : subtype l2 X
  subtype-finite-subtype = pr1 S

  type-finite-subtype : UU (l1 ⊔ l2)
  type-finite-subtype = type-subtype subtype-finite-subtype

  is-finite-type-finite-subtype : is-finite type-finite-subtype
  is-finite-type-finite-subtype = pr2 S

  finite-type-finite-subtype : Finite-Type (l1 ⊔ l2)
  finite-type-finite-subtype =
    (type-finite-subtype , is-finite-type-finite-subtype)

  number-of-elements-finite-subtype : ℕ
  number-of-elements-finite-subtype =
    number-of-elements-Finite-Type finite-type-finite-subtype
```

### The empty finite subtype

```agda
empty-finite-subtype :
  {l1 : Level} (l2 : Level) (X : UU l1) → finite-subtype l2 X
empty-finite-subtype l2 X =
  ( ( λ _ → raise-empty-Prop l2) ,
    is-finite-is-empty (is-empty-raise-empty ∘ pr2))
```
