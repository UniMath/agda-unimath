# Full subuniverses

```agda
module foundation.full-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.full-subtypes
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "full subuniverse" Agda=full-subuniverse}} of a
[universe](foundation.universe-levels.md) contains every type.

## Definitions

### Full subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-full-subuniverse-Prop : Prop (lsuc l1 ⊔ l2)
  is-full-subuniverse-Prop = is-full-subtype-Prop P

  is-full-subuniverse : UU (lsuc l1 ⊔ l2)
  is-full-subuniverse = is-full-subtype P

  is-prop-is-full-subuniverse : is-prop is-full-subuniverse
  is-prop-is-full-subuniverse = is-prop-is-full-subtype P
```

### The full subuniverse at universe levels

```agda
full-subuniverse : (l1 l2 : Level) → subuniverse l1 l2
full-subuniverse l1 l2 = full-subtype l2 (UU l1)

type-full-subuniverse : (l1 l2 : Level) → UU (lsuc l1 ⊔ l2)
type-full-subuniverse l1 l2 = type-subuniverse (full-subuniverse l1 l2)

module _
  {l1 l2 : Level}
  where

  is-in-full-subuniverse :
    (X : UU l1) → is-in-subuniverse (full-subuniverse l1 l2) X
  is-in-full-subuniverse =
    is-in-full-subtype {l1 = lsuc l1} {l2 = l2} {A = UU l1}

  inclusion-full-subuniverse : type-full-subuniverse l1 l2 → UU l1
  inclusion-full-subuniverse = inclusion-subuniverse (full-subuniverse l1 l2)

  is-equiv-inclusion-full-subuniverse : is-equiv inclusion-full-subuniverse
  is-equiv-inclusion-full-subuniverse =
    is-equiv-inclusion-full-subtype {l1 = lsuc l1} {l2 = l2} {A = UU l1}

  equiv-inclusion-full-subuniverse :
    type-full-subuniverse l1 l2 ≃ UU l1
  equiv-inclusion-full-subuniverse =
    inclusion-full-subuniverse , is-equiv-inclusion-full-subuniverse

  inv-equiv-inclusion-full-subuniverse :
    UU l1 ≃ type-full-subuniverse l1 l2
  inv-equiv-inclusion-full-subuniverse =
    inv-equiv equiv-inclusion-full-subuniverse
```

## Properties

### A subuniverse is full if and only if the inclusion is an equivalence

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-equiv-inclusion-is-full-subuniverse :
    is-full-subuniverse P → is-equiv (inclusion-subuniverse P)
  is-equiv-inclusion-is-full-subuniverse =
    is-equiv-inclusion-is-full-subtype P

  equiv-inclusion-is-full-subuniverse :
    is-full-subuniverse P → type-subuniverse P ≃ UU l1
  pr1 (equiv-inclusion-is-full-subuniverse H) = inclusion-subuniverse P
  pr2 (equiv-inclusion-is-full-subuniverse H) =
    is-equiv-inclusion-is-full-subuniverse H

  inv-equiv-inclusion-is-full-subuniverse :
    is-full-subuniverse P → UU l1 ≃ type-subuniverse P
  inv-equiv-inclusion-is-full-subuniverse H =
    inv-equiv (equiv-inclusion-is-full-subuniverse H)

  is-full-is-equiv-inclusion-subuniverse :
    is-equiv (inclusion-subuniverse P) → is-full-subuniverse P
  is-full-is-equiv-inclusion-subuniverse =
    is-full-is-equiv-inclusion-subtype P
```
