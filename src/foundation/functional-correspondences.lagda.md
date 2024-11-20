# Functional correspondences

```agda
module foundation.functional-correspondences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A
{{#concept "functional (dependent) correspondence" Agda=is-functional-correspondence}}
is a dependent binary correspondence `C : Π (a : A) → B a → 𝒰` from a type `A`
to a type family `B` over `A` such that for every `a : A` the type family
`C a : B a → Type` is [torsorial](foundation-core.torsorial-type-families.md).
The type of dependent functions from `A` to `B` is equivalent to the type of
functional dependent correspondences.

## Definition

```agda
is-functional-correspondence-Prop :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (a : A) → B a → UU l3) →
  Prop (l1 ⊔ l2 ⊔ l3)
is-functional-correspondence-Prop {A = A} {B} C =
  Π-Prop A (λ x → is-torsorial-Prop (C x))

is-functional-correspondence :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (a : A) → B a → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
is-functional-correspondence C =
  type-Prop (is-functional-correspondence-Prop C)

is-prop-is-functional-correspondence :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (a : A) → B a → UU l3) →
  is-prop (is-functional-correspondence C)
is-prop-is-functional-correspondence C =
  is-prop-type-Prop (is-functional-correspondence-Prop C)

functional-correspondence :
  {l1 l2 : Level} (l3 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
functional-correspondence l3 A B =
  type-subtype (is-functional-correspondence-Prop {l3 = l3} {A} {B})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : functional-correspondence l3 A B)
  where

  correspondence-functional-correspondence :
    (x : A) → B x → UU l3
  correspondence-functional-correspondence = pr1 C

  is-functional-functional-correspondence :
    is-functional-correspondence
      correspondence-functional-correspondence
  is-functional-functional-correspondence =
    pr2 C
```

## Properties

### Characterization of equality in the type of functional dependent correspondences

```agda
equiv-functional-correspondence :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (C : functional-correspondence l3 A B)
  (D : functional-correspondence l4 A B) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-functional-correspondence {A = A} {B} C D =
  (x : A) (y : B x) →
  correspondence-functional-correspondence C x y ≃
  correspondence-functional-correspondence D x y

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : functional-correspondence l3 A B)
  where

  id-equiv-functional-correspondence :
    equiv-functional-correspondence C C
  id-equiv-functional-correspondence x y = id-equiv

  is-torsorial-equiv-functional-correspondence :
    is-torsorial (equiv-functional-correspondence C)
  is-torsorial-equiv-functional-correspondence =
    is-torsorial-Eq-subtype
      ( is-torsorial-Eq-Π
        ( λ x →
          is-torsorial-equiv-fam
            ( correspondence-functional-correspondence
              C x)))
      ( is-prop-is-functional-correspondence)
      ( correspondence-functional-correspondence C)
      ( id-equiv-functional-correspondence)
      ( is-functional-functional-correspondence C)

  equiv-eq-functional-correspondence :
    (D : functional-correspondence l3 A B) →
    (C ＝ D) → equiv-functional-correspondence C D
  equiv-eq-functional-correspondence .C refl =
    id-equiv-functional-correspondence

  is-equiv-equiv-eq-functional-correspondence :
    (D : functional-correspondence l3 A B) →
    is-equiv (equiv-eq-functional-correspondence D)
  is-equiv-equiv-eq-functional-correspondence =
    fundamental-theorem-id
      is-torsorial-equiv-functional-correspondence
      equiv-eq-functional-correspondence

  extensionality-functional-correspondence :
    (D : functional-correspondence l3 A B) →
    (C ＝ D) ≃ equiv-functional-correspondence C D
  pr1 (extensionality-functional-correspondence D) =
    equiv-eq-functional-correspondence D
  pr2 (extensionality-functional-correspondence D) =
    is-equiv-equiv-eq-functional-correspondence D

  eq-equiv-functional-correspondence :
    (D : functional-correspondence l3 A B) →
    equiv-functional-correspondence C D → C ＝ D
  eq-equiv-functional-correspondence D =
    map-inv-equiv (extensionality-functional-correspondence D)
```

### The type of dependent functions `(x : A) → B x` is equivalent to the type of functional dependent correspondences from `A` to `B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  functional-correspondence-function :
    ((x : A) → B x) → functional-correspondence l2 A B
  pr1 (functional-correspondence-function f) x y = f x ＝ y
  pr2 (functional-correspondence-function f) x =
    is-torsorial-Id (f x)

  function-functional-correspondence :
    {l3 : Level} → functional-correspondence l3 A B → ((x : A) → B x)
  function-functional-correspondence C x =
    pr1 (center (is-functional-functional-correspondence C x))

  is-retraction-function-functional-correspondence :
    (f : (x : A) → B x) →
    function-functional-correspondence
      ( functional-correspondence-function f) ＝ f
  is-retraction-function-functional-correspondence f =
    eq-htpy
      ( λ x →
        ap pr1
          ( contraction
            ( is-functional-functional-correspondence
              ( functional-correspondence-function f)
              ( x))
            ( f x , refl)))

  module _
    {l3 : Level} (C : functional-correspondence l3 A B)
    where

    map-is-section-function-functional-correspondence :
      (x : A) (y : B x) →
      function-functional-correspondence C x ＝ y →
      correspondence-functional-correspondence C x y
    map-is-section-function-functional-correspondence x ._ refl =
      pr2 ( center (is-functional-functional-correspondence C x))

    is-equiv-map-is-section-function-functional-correspondence :
      (x : A) (y : B x) →
      is-equiv (map-is-section-function-functional-correspondence x y)
    is-equiv-map-is-section-function-functional-correspondence
      x =
      fundamental-theorem-id
        ( is-functional-functional-correspondence C x)
        ( map-is-section-function-functional-correspondence x)

    equiv-is-section-function-functional-correspondence :
      equiv-functional-correspondence
        ( functional-correspondence-function
          ( function-functional-correspondence C))
        ( C)
    pr1 ( equiv-is-section-function-functional-correspondence x y) =
      map-is-section-function-functional-correspondence x y
    pr2 (equiv-is-section-function-functional-correspondence x y) =
      is-equiv-map-is-section-function-functional-correspondence x y

  is-section-function-functional-correspondence :
    (C : functional-correspondence l2 A B) →
    functional-correspondence-function (function-functional-correspondence C) ＝
    C
  is-section-function-functional-correspondence C =
    eq-equiv-functional-correspondence
      ( functional-correspondence-function
        ( function-functional-correspondence C))
      ( C)
      ( equiv-is-section-function-functional-correspondence C)

  is-equiv-functional-correspondence-function :
    is-equiv functional-correspondence-function
  is-equiv-functional-correspondence-function =
    is-equiv-is-invertible
      function-functional-correspondence
      is-section-function-functional-correspondence
      is-retraction-function-functional-correspondence

  equiv-functional-correspondence-function :
    ((x : A) → B x) ≃ functional-correspondence l2 A B
  pr1 equiv-functional-correspondence-function =
    functional-correspondence-function
  pr2 equiv-functional-correspondence-function =
    is-equiv-functional-correspondence-function
```
