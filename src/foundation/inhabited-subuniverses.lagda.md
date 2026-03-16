# Inhabited subuniverses

```agda
module foundation.inhabited-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A [subuniverse](foundation.subuniverses.md) is
{{#concept "inhabited" Disambiguation="subuniverse" Agda=is-inhabited-subuniverse Agda=inhabited-subuniverse}}
if its underlying type is [inhabited](foundation.inhabited-types.md). This is
exactly an [inhabited subtype](foundation.inhabited-subtypes.md) of the
universe.

## Definitions

### The predicate on a subuniverse of being inhabited

```agda
is-inhabited-subuniverse-Prop :
  {l1 l2 : Level} → subuniverse l1 l2 → Prop (lsuc l1 ⊔ l2)
is-inhabited-subuniverse-Prop = is-inhabited-subtype-Prop

is-inhabited-subuniverse :
  {l1 l2 : Level} → subuniverse l1 l2 → UU (lsuc l1 ⊔ l2)
is-inhabited-subuniverse = is-inhabited-subtype
```

### The type of inhabited subuniverses

```agda
inhabited-subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
inhabited-subuniverse l1 l2 = inhabited-subtype l2 (UU l1)

module _
  {l1 l2 : Level} (P : inhabited-subuniverse l1 l2)
  where

  subtype-inhabited-subuniverse : subtype l2 (UU l1)
  subtype-inhabited-subuniverse = subtype-inhabited-subtype P

  subuniverse-inhabited-subuniverse : subuniverse l1 l2
  subuniverse-inhabited-subuniverse = subtype-inhabited-subuniverse

  is-inhabited-subuniverse-inhabited-subuniverse :
    is-inhabited-subuniverse subuniverse-inhabited-subuniverse
  is-inhabited-subuniverse-inhabited-subuniverse =
    is-inhabited-subtype-inhabited-subtype P

  type-inhabited-subuniverse : UU (lsuc l1 ⊔ l2)
  type-inhabited-subuniverse = type-inhabited-subtype P

  inhabited-type-inhabited-subuniverse : Inhabited-Type (lsuc l1 ⊔ l2)
  inhabited-type-inhabited-subuniverse = inhabited-type-inhabited-subtype P

  is-in-inhabited-subuniverse : UU l1 → UU l2
  is-in-inhabited-subuniverse = is-in-inhabited-subtype P

  is-prop-is-in-inhabited-subuniverse :
    (X : UU l1) → is-prop (is-in-inhabited-subuniverse X)
  is-prop-is-in-inhabited-subuniverse =
    is-prop-is-in-inhabited-subtype P

  inclusion-inhabited-subuniverse : type-inhabited-subuniverse → UU l1
  inclusion-inhabited-subuniverse = inclusion-inhabited-subtype P

  ap-inclusion-inhabited-subuniverse :
    (X Y : type-inhabited-subuniverse) →
    X ＝ Y →
    ( inclusion-inhabited-subuniverse X ＝
      inclusion-inhabited-subuniverse Y)
  ap-inclusion-inhabited-subuniverse = ap-inclusion-inhabited-subtype P

  is-in-inhabited-subuniverse-inclusion-inhabited-subuniverse :
    (X : type-inhabited-subuniverse) →
    is-in-inhabited-subuniverse (inclusion-inhabited-subuniverse X)
  is-in-inhabited-subuniverse-inclusion-inhabited-subuniverse =
    is-in-inhabited-subtype-inclusion-inhabited-subtype P
```

## Properties

### Characterization of equality of inhabited subuniverses

```agda
has-same-types-inhabited-subuniverse-Prop :
  {l1 l2 l3 : Level} →
  inhabited-subuniverse l1 l2 → inhabited-subuniverse l1 l3 →
  Prop (lsuc l1 ⊔ l2 ⊔ l3)
has-same-types-inhabited-subuniverse-Prop =
  has-same-elements-inhabited-subtype-Prop

has-same-types-inhabited-subuniverse :
  {l1 l2 l3 : Level} →
  inhabited-subuniverse l1 l2 →
  inhabited-subuniverse l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
has-same-types-inhabited-subuniverse = has-same-elements-inhabited-subtype

is-prop-has-same-types-inhabited-subuniverse :
  {l1 l2 l3 : Level} →
  (P : inhabited-subuniverse l1 l2)
  (Q : inhabited-subuniverse l1 l3) →
  is-prop (has-same-types-inhabited-subuniverse P Q)
is-prop-has-same-types-inhabited-subuniverse =
  is-prop-has-same-elements-inhabited-subtype

module _
  {l1 l2 : Level} (P : inhabited-subuniverse l1 l2)
  where

  refl-has-same-types-inhabited-subuniverse :
    has-same-types-inhabited-subuniverse P P
  refl-has-same-types-inhabited-subuniverse =
    refl-has-same-elements-inhabited-subtype P

  is-torsorial-has-same-types-inhabited-subuniverse :
    is-torsorial (has-same-types-inhabited-subuniverse P)
  is-torsorial-has-same-types-inhabited-subuniverse =
    is-torsorial-has-same-elements-inhabited-subtype P

  extensionality-inhabited-subuniverse :
    (Q : inhabited-subuniverse l1 l2) →
    (P ＝ Q) ≃ has-same-types-inhabited-subuniverse P Q
  extensionality-inhabited-subuniverse =
    extensionality-inhabited-subtype P

  has-same-elements-eq-inhabited-subuniverse :
    (Q : inhabited-subuniverse l1 l2) →
    (P ＝ Q) → has-same-types-inhabited-subuniverse P Q
  has-same-elements-eq-inhabited-subuniverse =
    has-same-elements-eq-inhabited-subtype P

  eq-has-same-types-inhabited-subuniverse :
    (Q : inhabited-subuniverse l1 l2) →
    has-same-types-inhabited-subuniverse P Q → P ＝ Q
  eq-has-same-types-inhabited-subuniverse =
    eq-has-same-elements-inhabited-subtype P

  refl-extensionality-inhabited-subuniverse :
    map-equiv (extensionality-inhabited-subuniverse P) refl ＝
    refl-has-same-types-inhabited-subuniverse
  refl-extensionality-inhabited-subuniverse =
    refl-extensionality-inhabited-subtype P
```
