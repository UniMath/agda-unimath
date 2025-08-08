# Finite subtypes

```agda
module univalent-combinatorics.finite-subtypes where
```

<details><summary>Imports</summary>

```agda
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
```
