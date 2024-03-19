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
open import foundation.span-diagrams
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **cofiber** of a map `f : A → B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the span `B ← A → 1`.

## Definitions

### The cofiber span diagram of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  span-diagram-cofiber : (A → B) → span-diagram l2 lzero l1
  span-diagram-cofiber f = make-span-diagram f (terminal-map A)
```

### The cofiber of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cofiber : (A → B) → UU (l1 ⊔ l2)
  cofiber f = standard-pushout (span-diagram-cofiber f)

  cocone-cofiber :
    (f : A → B) → cocone-span-diagram (span-diagram-cofiber f) (cofiber f)
  cocone-cofiber f = cocone-standard-pushout (span-diagram-cofiber f)

  inl-cofiber : (f : A → B) → B → cofiber f
  inl-cofiber f = left-map-cocone-span-diagram _ (cocone-cofiber f)

  inr-cofiber : (f : A → B) → unit → cofiber f
  inr-cofiber f = right-map-cocone-span-diagram _ (cocone-cofiber f)

  point-cofiber : (f : A → B) → cofiber f
  point-cofiber f = inr-cofiber f star

  cofiber-Pointed-Type : (f : A → B) → Pointed-Type (l1 ⊔ l2)
  pr1 (cofiber-Pointed-Type f) = cofiber f
  pr2 (cofiber-Pointed-Type f) = point-cofiber f

  universal-property-cofiber :
    (f : A → B) →
    universal-property-pushout (span-diagram-cofiber f) (cocone-cofiber f)
  universal-property-cofiber f =
    universal-property-pushout-standard-pushout (span-diagram-cofiber f)
```

## Properties

### The cofiber of an equivalence is contractible

Note that this is not a logical equivalence. Not every map whose cofibers are
all contractible is an equivalence. For instance, the cofiber of `X → 1` where
`X` is an [acyclic type](synthetic-homotopy-theory.acyclic-types.md) is by
definition contractible. Examples of noncontractible acyclic types include
[Hatcher's acyclic type](synthetic-homotopy-theory.hatchers-acyclic-type.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-contr-cofiber-is-equiv :
    is-equiv f → is-contr (cofiber f)
  is-contr-cofiber-is-equiv is-equiv-f =
    is-contr-is-equiv'
      ( unit)
      ( inr-cofiber f)
      ( is-equiv-right-map-cocone-universal-property-pushout
        ( span-diagram-cofiber f)
        ( cocone-cofiber f)
        ( is-equiv-f)
        ( universal-property-cofiber f))
      ( is-contr-unit)
```

### The cofiber of the point inclusion of `X` is equivalent to `X`

```agda
is-equiv-inl-cofiber-point :
  {l : Level} {B : UU l} (b : B) → is-equiv (inl-cofiber (point b))
is-equiv-inl-cofiber-point {B = B} b =
  is-equiv-left-map-cocone-universal-property-pushout
    ( span-diagram-cofiber (point b))
    ( cocone-cofiber (point b))
    ( is-equiv-id)
    ( universal-property-pushout-standard-pushout
      ( span-diagram-cofiber (point b)))
```
