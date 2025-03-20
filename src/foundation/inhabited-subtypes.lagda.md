# Inhabited subtypes

```agda
open import foundation.function-extensionality-axiom

module
  foundation.inhabited-subtypes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types funext
open import foundation.propositional-truncations funext
open import foundation.subtype-identity-principle
open import foundation.subtypes funext
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An inhabited subtype of a type `A` is a subtype `P` of `A` such that the
underlying type of `P` is inhabited.

```agda
is-inhabited-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-inhabited-subtype-Prop P = is-inhabited-Prop (type-subtype P)

is-inhabited-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-inhabited-subtype P = type-Prop (is-inhabited-subtype-Prop P)

inhabited-subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
inhabited-subtype l2 A = type-subtype (is-inhabited-subtype-Prop {l2 = l2} {A})

module _
  {l1 l2 : Level} {A : UU l1} (P : inhabited-subtype l2 A)
  where

  subtype-inhabited-subtype : subtype l2 A
  subtype-inhabited-subtype = pr1 P

  is-inhabited-subtype-inhabited-subtype :
    is-inhabited-subtype subtype-inhabited-subtype
  is-inhabited-subtype-inhabited-subtype = pr2 P

  type-inhabited-subtype : UU (l1 ⊔ l2)
  type-inhabited-subtype = type-subtype subtype-inhabited-subtype

  inhabited-type-inhabited-subtype : Inhabited-Type (l1 ⊔ l2)
  pr1 inhabited-type-inhabited-subtype = type-inhabited-subtype
  pr2 inhabited-type-inhabited-subtype =
    is-inhabited-subtype-inhabited-subtype

  is-in-inhabited-subtype : A → UU l2
  is-in-inhabited-subtype = is-in-subtype subtype-inhabited-subtype

  is-prop-is-in-inhabited-subtype :
    (x : A) → is-prop (is-in-inhabited-subtype x)
  is-prop-is-in-inhabited-subtype =
    is-prop-is-in-subtype subtype-inhabited-subtype

  inclusion-inhabited-subtype : type-inhabited-subtype → A
  inclusion-inhabited-subtype = inclusion-subtype subtype-inhabited-subtype

  ap-inclusion-inhabited-subtype :
    (x y : type-inhabited-subtype) →
    x ＝ y → (inclusion-inhabited-subtype x ＝ inclusion-inhabited-subtype y)
  ap-inclusion-inhabited-subtype =
    ap-inclusion-subtype subtype-inhabited-subtype

  is-in-inhabited-subtype-inclusion-inhabited-subtype :
    (x : type-inhabited-subtype) →
    is-in-inhabited-subtype (inclusion-inhabited-subtype x)
  is-in-inhabited-subtype-inclusion-inhabited-subtype =
    is-in-subtype-inclusion-subtype subtype-inhabited-subtype
```

## Properties

### Characterization of equality of inhabited subtypes

```agda
has-same-elements-inhabited-subtype-Prop :
  {l1 l2 l3 : Level} {A : UU l1} →
  inhabited-subtype l2 A → inhabited-subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
has-same-elements-inhabited-subtype-Prop P Q =
  has-same-elements-subtype-Prop
    ( subtype-inhabited-subtype P)
    ( subtype-inhabited-subtype Q)

has-same-elements-inhabited-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  inhabited-subtype l2 A → inhabited-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
has-same-elements-inhabited-subtype P Q =
  type-Prop (has-same-elements-inhabited-subtype-Prop P Q)

is-prop-has-same-elements-inhabited-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  (P : inhabited-subtype l2 A) (Q : inhabited-subtype l3 A) →
  is-prop (has-same-elements-inhabited-subtype P Q)
is-prop-has-same-elements-inhabited-subtype P Q =
  is-prop-type-Prop (has-same-elements-inhabited-subtype-Prop P Q)

module _
  {l1 l2 : Level} {A : UU l1} (P : inhabited-subtype l2 A)
  where

  refl-has-same-elements-inhabited-subtype :
    has-same-elements-inhabited-subtype P P
  refl-has-same-elements-inhabited-subtype =
    refl-has-same-elements-subtype (subtype-inhabited-subtype P)

  is-torsorial-has-same-elements-inhabited-subtype :
    is-torsorial (has-same-elements-inhabited-subtype P)
  is-torsorial-has-same-elements-inhabited-subtype =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype
        ( subtype-inhabited-subtype P))
      ( λ Q → is-prop-type-trunc-Prop)
      ( subtype-inhabited-subtype P)
      ( refl-has-same-elements-inhabited-subtype)
      ( is-inhabited-subtype-inhabited-subtype P)

  extensionality-inhabited-subtype :
    (Q : inhabited-subtype l2 A) → (P ＝ Q) ≃
    has-same-elements-inhabited-subtype P Q
  extensionality-inhabited-subtype Q =
    ( extensionality-subtype
      ( subtype-inhabited-subtype P)
      ( subtype-inhabited-subtype Q)) ∘e
    ( extensionality-type-subtype' is-inhabited-subtype-Prop P Q)

  has-same-elements-eq-inhabited-subtype :
    (Q : inhabited-subtype l2 A) →
    (P ＝ Q) → has-same-elements-inhabited-subtype P Q
  has-same-elements-eq-inhabited-subtype Q =
    map-equiv (extensionality-inhabited-subtype Q)

  eq-has-same-elements-inhabited-subtype :
    (Q : inhabited-subtype l2 A) →
    has-same-elements-inhabited-subtype P Q → P ＝ Q
  eq-has-same-elements-inhabited-subtype Q =
    map-inv-equiv (extensionality-inhabited-subtype Q)

  refl-extensionality-inhabited-subtype :
    map-equiv (extensionality-inhabited-subtype P) refl ＝
    refl-has-same-elements-inhabited-subtype
  refl-extensionality-inhabited-subtype = refl
```
