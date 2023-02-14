#  Inhabited types

```agda
module foundation.inhabited-types where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.univalence
open import foundation.universe-levels
```

## Idea

Inhabited types are types equipped with an element of its propositional truncation.

## Definitions

### Inhabited types

```agda
is-inhabited-Prop : {l : Level} → UU l → Prop l
is-inhabited-Prop X = trunc-Prop X

is-inhabited : {l : Level} → UU l → UU l
is-inhabited X = type-Prop (is-inhabited-Prop X)

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

  is-contr-total-equiv-Inhabited-Type :
    is-contr (Σ (Inhabited-Type l) (equiv-Inhabited-Type X))
  is-contr-total-equiv-Inhabited-Type =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv (type-Inhabited-Type X))
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
      is-contr-total-equiv-Inhabited-Type
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

  is-contr-total-equiv-Fam-Inhabited-Types :
    is-contr (Σ (Fam-Inhabited-Types l2 X) (equiv-Fam-Inhabited-Types Y))
  is-contr-total-equiv-Fam-Inhabited-Types =
    is-contr-total-Eq-Π
      ( λ x → equiv-Inhabited-Type (Y x))
      ( λ x → is-contr-total-equiv-Inhabited-Type (Y x))

  equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → (Y ＝ Z) → equiv-Fam-Inhabited-Types Y Z
  equiv-eq-Fam-Inhabited-Types .Y refl = id-equiv-Fam-Inhabited-Types

  is-equiv-equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → is-equiv (equiv-eq-Fam-Inhabited-Types Z)
  is-equiv-equiv-eq-Fam-Inhabited-Types =
    fundamental-theorem-id
      is-contr-total-equiv-Fam-Inhabited-Types
      equiv-eq-Fam-Inhabited-Types
```

## See also

- The notion of *nonempty types* is treated in
  [`foundation.empty-types`](foundation.empty-types.html).
  In particular, every inhabited type is nonempty.

- For the notion of *pointed types*, see
  [`structured-types.pointed-types`](structured-types.pointed-types.html).