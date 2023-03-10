# Cofibers

```agda
module synthetic-homotopy-theory.cofibers where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The cofiber of a map `f : A → B` is the pushout of the span `1 ← A → B`.

## Definition

```agda
cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
cofiber {A = A} f = pushout f (const A unit star)

cocone-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  cocone f (const A unit star) (cofiber f)
cocone-cofiber {A = A} f = cocone-pushout f (const A unit star)

inl-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → B → cofiber f
inl-cofiber {A = A} f = pr1 (cocone-cofiber f)

inr-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → unit → cofiber f
inr-cofiber f = pr1 (pr2 (cocone-cofiber f))

pt-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → cofiber f
pt-cofiber {A = A} f = inr-cofiber f star

cofiber-ptd :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → Pointed-Type (l1 ⊔ l2)
cofiber-ptd f = pair (cofiber f) (pt-cofiber f)

up-cofiber :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( {l : Level} →
    universal-property-pushout l f (const A unit star) (cocone-cofiber f))
up-cofiber {A = A} f = up-pushout f (const A unit star)

```

## Properties

```agda
is-contr-cofiber-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-contr (cofiber f)
is-contr-cofiber-is-equiv {A = A} {B} f is-equiv-f =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-cofiber f)))
    ( is-equiv-universal-property-pushout
      ( f)
      ( const A unit star)
      ( cocone-cofiber f)
      ( is-equiv-f)
      ( up-cofiber f))
    ( is-contr-unit)
```
