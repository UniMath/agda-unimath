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

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **cofiber** of a map `f : A → B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the span `1 ← A → B`.

## Definitions

### The cofiber of a map

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

point-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → cofiber f
point-cofiber {A = A} f = inr-cofiber f star

cofiber-Pointed-Type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → Pointed-Type (l1 ⊔ l2)
pr1 (cofiber-Pointed-Type f) = cofiber f
pr2 (cofiber-Pointed-Type f) = point-cofiber f

universal-property-cofiber :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( {l : Level} →
    universal-property-pushout l f (const A unit star) (cocone-cofiber f))
universal-property-cofiber {A = A} f = up-pushout f (const A unit star)
```

## Properties

### The cofiber of an equivalence is contractible

Note that this is not a logical equivalence. The cofiber of `X → 1` where `X` is
an [acyclic type](synthetic-homotopy-theory.acyclic-types.md) is by definition
contractible. Examples of noncontractible acyclic types include
[Hatcher's acyclic type](synthetic-homotopy-theory.hatchers-acyclic-type.md).

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
      ( universal-property-cofiber f))
    ( is-contr-unit)
```

### The cofiber of the point inclusion of `X` is equivalent to `X`

```agda
is-equiv-inl-cofiber-point :
  {l : Level} {B : UU l} (b : B) → is-equiv (inl-cofiber (point b))
is-equiv-inl-cofiber-point {l} {B} b =
  is-equiv-universal-property-pushout'
    ( const unit B b)
    ( const unit unit star)
    ( cocone-pushout (const unit B b) (const unit unit star))
    ( is-equiv-is-contr (const unit unit star) is-contr-unit is-contr-unit)
    ( up-pushout (const unit B b) (const unit unit star))
```
