# Transport-split type families

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.transport-split-type-families
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalence-injective-type-families funext univalence
open import foundation.equivalences funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types funext
open import foundation.telescopes
open import foundation.transport-along-identifications
open import foundation.univalent-type-families funext univalence
open import foundation.universal-property-identity-systems funext
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "transport-split" Disambiguation="type family" Agda=is-transport-split}}
if the map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

admits a [section](foundation-core.sections.md) for every `x y : A`. By a
corollary of
[the fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
every transport-split type family is
[univalent](foundation.univalent-type-families.md), meaning that `equiv-tr B` is
in fact an [equivalence](foundation-core.equivalences.md) for all `x y : A`.

## Definition

### Transport-split type families

```agda
is-transport-split :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-transport-split {A = A} B =
  (x y : A) → section (λ (p : x ＝ y) → equiv-tr B p)
```

## Properties

### Transport-split type families are equivalence injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equivalence-injective-is-transport-split :
    is-transport-split B → is-equivalence-injective B
  is-equivalence-injective-is-transport-split s {x} {y} =
    map-section (equiv-tr B) (s x y)
```

### Transport-split type families are univalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-transport-split-is-univalent :
    is-univalent B → is-transport-split B
  is-transport-split-is-univalent U x y = section-is-equiv (U x y)

  is-univalent-is-transport-split :
    is-transport-split B → is-univalent B
  is-univalent-is-transport-split s x =
    fundamental-theorem-id-section x (λ y → equiv-tr B) (s x)
```

### The type `is-transport-split` is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-is-transport-split :
    is-proof-irrelevant (is-transport-split B)
  is-proof-irrelevant-is-transport-split s =
    is-contr-iterated-Π 2
      ( λ x y →
        is-contr-section-is-equiv (is-univalent-is-transport-split s x y))

  is-prop-is-transport-split :
    is-prop (is-transport-split B)
  is-prop-is-transport-split =
    is-prop-is-proof-irrelevant is-proof-irrelevant-is-transport-split
```

### Assuming the univalence axiom, type families are transport-split if and only if they are embeddings as maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-emb-is-transport-split : is-transport-split B → is-emb B
  is-emb-is-transport-split s =
    is-emb-is-univalent (is-univalent-is-transport-split s)

  is-transport-split-is-emb : is-emb B → is-transport-split B
  is-transport-split-is-emb H =
    is-transport-split-is-univalent (is-univalent-is-emb H)
```

### Transport-split type families satisfy equivalence induction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (s : is-transport-split B)
  where

  is-torsorial-fam-equiv-is-transport-split :
    {x : A} → is-torsorial (λ y → B x ≃ B y)
  is-torsorial-fam-equiv-is-transport-split =
    is-torsorial-fam-equiv-is-univalent (is-univalent-is-transport-split s)

  dependent-universal-property-identity-system-fam-equiv-is-transport-split :
    {x : A} →
    dependent-universal-property-identity-system (λ y → B x ≃ B y) id-equiv
  dependent-universal-property-identity-system-fam-equiv-is-transport-split =
    dependent-universal-property-identity-system-is-torsorial
      ( id-equiv)
      ( is-torsorial-fam-equiv-is-transport-split)
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Preunivalent type families](foundation.preunivalent-type-families.md)
