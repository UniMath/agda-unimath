# Inhabited types

```agda
module foundation.inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

**Inhabited types** are types equipped with an element of its propositional
truncation.

**Remark:** This contrasts with the definition of
[pointed types](structured-types.pointed-types.md) in that we do not discern
between proofs of inhabitedness, so that it is merely a property of the type to
be inhabited.

## Definitions

### Inhabited types

```agda
is-inhabited-Prop : {l : Level} → UU l → Prop l
is-inhabited-Prop X = trunc-Prop X

is-inhabited : {l : Level} → UU l → UU l
is-inhabited X = type-Prop (is-inhabited-Prop X)

is-property-is-inhabited : {l : Level} (X : UU l) → is-prop (is-inhabited X)
is-property-is-inhabited X = is-prop-type-Prop (is-inhabited-Prop X)

Inhabited-Type : (l : Level) → UU (lsuc l)
Inhabited-Type l = Σ (UU l) is-inhabited

module _
  {l : Level} (X : Inhabited-Type l)
  where

  type-Inhabited-Type : UU l
  type-Inhabited-Type = pr1 X

  is-inhabited-type-Inhabited-Type : type-trunc-Prop type-Inhabited-Type
  is-inhabited-type-Inhabited-Type = pr2 X
```

### Families of inhabited types

```agda
Fam-Inhabited-Types :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types l2 X = X → Inhabited-Type l2

module _
  {l1 l2 : Level} {X : UU l1} (Y : Fam-Inhabited-Types l2 X)
  where

  type-Fam-Inhabited-Types : X → UU l2
  type-Fam-Inhabited-Types x = type-Inhabited-Type (Y x)

  is-inhabited-type-Fam-Inhabited-Types :
    (x : X) → type-trunc-Prop (type-Fam-Inhabited-Types x)
  is-inhabited-type-Fam-Inhabited-Types x =
    is-inhabited-type-Inhabited-Type (Y x)

  total-Fam-Inhabited-Types : UU (l1 ⊔ l2)
  total-Fam-Inhabited-Types = Σ X type-Fam-Inhabited-Types
```

## Properties

### Characterization of equality of inhabited types

```agda
equiv-Inhabited-Type :
  {l1 l2 : Level} → Inhabited-Type l1 → Inhabited-Type l2 → UU (l1 ⊔ l2)
equiv-Inhabited-Type X Y = type-Inhabited-Type X ≃ type-Inhabited-Type Y

module _
  {l : Level} (X : Inhabited-Type l)
  where

  is-torsorial-equiv-Inhabited-Type :
    is-torsorial (equiv-Inhabited-Type X)
  is-torsorial-equiv-Inhabited-Type =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv (type-Inhabited-Type X))
      ( λ X → is-prop-type-trunc-Prop)
      ( type-Inhabited-Type X)
      ( id-equiv)
      ( is-inhabited-type-Inhabited-Type X)

  equiv-eq-Inhabited-Type :
    (Y : Inhabited-Type l) → (X ＝ Y) → equiv-Inhabited-Type X Y
  equiv-eq-Inhabited-Type .X refl = id-equiv

  is-equiv-equiv-eq-Inhabited-Type :
    (Y : Inhabited-Type l) → is-equiv (equiv-eq-Inhabited-Type Y)
  is-equiv-equiv-eq-Inhabited-Type =
    fundamental-theorem-id
      is-torsorial-equiv-Inhabited-Type
      equiv-eq-Inhabited-Type

  extensionality-Inhabited-Type :
    (Y : Inhabited-Type l) → (X ＝ Y) ≃ equiv-Inhabited-Type X Y
  pr1 (extensionality-Inhabited-Type Y) = equiv-eq-Inhabited-Type Y
  pr2 (extensionality-Inhabited-Type Y) = is-equiv-equiv-eq-Inhabited-Type Y

  eq-equiv-Inhabited-Type :
    (Y : Inhabited-Type l) → equiv-Inhabited-Type X Y → (X ＝ Y)
  eq-equiv-Inhabited-Type Y =
    map-inv-equiv (extensionality-Inhabited-Type Y)
```

### Characterization of equality of families of inhabited types

```agda
equiv-Fam-Inhabited-Types :
  {l1 l2 l3 : Level} {X : UU l1} →
  Fam-Inhabited-Types l2 X → Fam-Inhabited-Types l3 X → UU (l1 ⊔ l2 ⊔ l3)
equiv-Fam-Inhabited-Types {X = X} Y Z =
  (x : X) → equiv-Inhabited-Type (Y x) (Z x)

module _
  {l1 l2 : Level} {X : UU l1} (Y : Fam-Inhabited-Types l2 X)
  where

  id-equiv-Fam-Inhabited-Types : equiv-Fam-Inhabited-Types Y Y
  id-equiv-Fam-Inhabited-Types = id-equiv-fam (type-Fam-Inhabited-Types Y)

  is-torsorial-equiv-Fam-Inhabited-Types :
    is-torsorial (equiv-Fam-Inhabited-Types Y)
  is-torsorial-equiv-Fam-Inhabited-Types =
    is-torsorial-Eq-Π (λ x → is-torsorial-equiv-Inhabited-Type (Y x))

  equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → (Y ＝ Z) → equiv-Fam-Inhabited-Types Y Z
  equiv-eq-Fam-Inhabited-Types .Y refl = id-equiv-Fam-Inhabited-Types

  is-equiv-equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → is-equiv (equiv-eq-Fam-Inhabited-Types Z)
  is-equiv-equiv-eq-Fam-Inhabited-Types =
    fundamental-theorem-id
      is-torsorial-equiv-Fam-Inhabited-Types
      equiv-eq-Fam-Inhabited-Types
```

### Inhabited types are closed under Σ

```agda
is-inhabited-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-inhabited X → ((x : X) → is-inhabited (Y x)) → is-inhabited (Σ X Y)
is-inhabited-Σ {l1} {l2} {X} {Y} H K =
  apply-twice-universal-property-trunc-Prop' H K
    ( is-inhabited-Prop (Σ X Y))
    ( λ x y → unit-trunc-Prop (x , y))

Σ-Inhabited-Type :
  {l1 l2 : Level} (X : Inhabited-Type l1)
  (Y : type-Inhabited-Type X → Inhabited-Type l2) → Inhabited-Type (l1 ⊔ l2)
pr1 (Σ-Inhabited-Type X Y) =
  Σ (type-Inhabited-Type X) (λ x → type-Inhabited-Type (Y x))
pr2 (Σ-Inhabited-Type X Y) =
  is-inhabited-Σ
    ( is-inhabited-type-Inhabited-Type X)
    ( λ x → is-inhabited-type-Inhabited-Type (Y x))
```

### The base of an inhabited Σ-type is inhabited

```agda
is-inhabited-base-is-inhabited-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-inhabited (Σ X Y) → is-inhabited X
is-inhabited-base-is-inhabited-Σ = map-trunc-Prop pr1
```

### Inhabited types are closed under maps

```agda
map-is-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : A → B) → is-inhabited A → is-inhabited B
map-is-inhabited f = map-trunc-Prop f
```

### Contractible types are inhabited

```agda
is-inhabited-is-contr :
  {l1 : Level} {A : UU l1} → is-contr A → is-inhabited A
is-inhabited-is-contr p =
  unit-trunc-Prop (center p)
```

### Inhabited propositions are contractible

```agda
is-contr-is-inhabited-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → is-inhabited A → is-contr A
is-contr-is-inhabited-is-prop {A = A} p h =
  apply-universal-property-trunc-Prop
    ( h)
    ( is-contr-Prop A)
    ( λ a → a , eq-is-prop' p a)
```

### Contractibility of the base of a dependent sum

Given a type `A` and a type family over it `B`, then if the dependent sum
`Σ A B` is contractible, it follows that if there merely exists a section
`(x : A) → B x`, then `A` is contractible.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    is-contr-base-is-contr-Σ :
      is-inhabited ((x : A) → B x) → is-contr (Σ A B) → is-contr A
    is-contr-base-is-contr-Σ s is-contr-ΣAB =
      rec-trunc-Prop
        ( is-contr-Prop A)
        ( λ s → is-contr-base-is-contr-Σ' A B s is-contr-ΣAB)
        ( s)
```

## See also

- The notion of _nonempty types_ is treated in
  [`foundation.empty-types`](foundation.empty-types.md). In particular, every
  inhabited type is nonempty.
- For the notion of _pointed types_, see
  [`structured-types.pointed-types`](structured-types.pointed-types.md).
