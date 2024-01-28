# Transport-split type families

```agda
module foundation.transport-split-type-families where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-injective-type-families
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sections
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "transport-split" Disambiguation="type family" Agda=is-transport-split}}
if the map

```text
  equiv-tr : x ＝ y → B x ≃ B y
```

admits a [section](foundation-core.section.md) for every `x y : A`.

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
  is-equivalence-injective-is-transport-split s {x} {y} e =
    map-section (equiv-tr B) (s x y) e
```

### Transport-split type families satisfy an equivalence induction principle

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (s : is-transport-split B)
  {P : {x y : A} → B x ≃ B y → UU l3}
  where

  ind-equiv-is-transport-split' :
    (f : {x y : A} (p : x ＝ y) → P (equiv-tr B p))
    {x y : A} (e : B x ≃ B y) → P e
  ind-equiv-is-transport-split' f {x} {y} e =
    tr P
      ( is-section-map-section (equiv-tr B) (s x y) e)
      ( f (map-section (equiv-tr B) (s x y) e))

  abstract
    ind-equiv-is-transport-split :
      (f : (x : A) → P (id-equiv {A = B x})) →
      {x y : A} (e : B x ≃ B y) → P e
    ind-equiv-is-transport-split f =
      ind-equiv-is-transport-split' (λ where refl → f _)
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md)
