# Cofibers of maps

```agda
module synthetic-homotopy-theory.cofibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "cofiber" Disambiguation="of a map of types" WD="mapping cone" WDID=Q306560 Agda=cofiber}}
of a map `f : A → B` is the [pushout](synthetic-homotopy-theory.pushouts.md) of
the span `B ← A → *`.

## Definitions

### The cofiber of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  cofiber : UU (l1 ⊔ l2)
  cofiber = pushout f (terminal-map A)

  cocone-cofiber : cocone f (terminal-map A) cofiber
  cocone-cofiber = cocone-pushout f (terminal-map A)

  inl-cofiber : B → cofiber
  inl-cofiber = pr1 cocone-cofiber

  inr-cofiber : unit → cofiber
  inr-cofiber = pr1 (pr2 cocone-cofiber)

  point-cofiber : cofiber
  point-cofiber = inr-cofiber star

  pointed-type-cofiber : Pointed-Type (l1 ⊔ l2)
  pointed-type-cofiber = (cofiber , point-cofiber)

  inr-pointed-map-cofiber : unit-Pointed-Type →∗ pointed-type-cofiber
  inr-pointed-map-cofiber = inclusion-point-Pointed-Type (pointed-type-cofiber)

  universal-property-cofiber :
    universal-property-pushout f (terminal-map A) cocone-cofiber
  universal-property-cofiber = up-pushout f (terminal-map A)

  equiv-up-cofiber :
    {l : Level} (X : UU l) → (cofiber → X) ≃ cocone f (terminal-map A) X
  equiv-up-cofiber X =
    ( cocone-map f (terminal-map A) cocone-cofiber ,
      universal-property-cofiber X)

  dependent-universal-property-cofiber :
    dependent-universal-property-pushout f (terminal-map A) cocone-cofiber
  dependent-universal-property-cofiber = dup-pushout f (terminal-map A)

  cogap-cofiber :
    {l : Level} {X : UU l} → cocone f (terminal-map A) X → cofiber → X
  cogap-cofiber = cogap f (terminal-map A)

  equiv-cogap-cofiber :
    {l : Level} (X : UU l) → cocone f (terminal-map A) X ≃ (cofiber → X)
  equiv-cogap-cofiber X =
    ( cogap-cofiber , is-equiv-map-inv-is-equiv (universal-property-cofiber X))

  dependent-cogap-cofiber :
    {l : Level} {P : cofiber → UU l}
    (c : dependent-cocone f (terminal-map A) (cocone-cofiber) P)
    (x : cofiber) → P x
  dependent-cogap-cofiber = dependent-cogap f (terminal-map A)
```

## Properties

### The cofiber of an equivalence is contractible

Note that this is not a logical equivalence. Not every map whose cofibers are
all contractible is an equivalence. For instance, the cofiber of `X → 1` where
`X` is an [acyclic type](synthetic-homotopy-theory.acyclic-types.md) is by
definition contractible. Examples of noncontractible acyclic types include
[Hatcher's acyclic type](synthetic-homotopy-theory.hatchers-acyclic-type.md).

```agda
is-contr-cofiber-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-contr (cofiber f)
is-contr-cofiber-is-equiv {A = A} f is-equiv-f =
  is-contr-equiv-unit'
    ( inr-cofiber f ,
      is-equiv-universal-property-pushout
        ( f)
        ( terminal-map A)
        ( cocone-cofiber f)
        ( is-equiv-f)
        ( universal-property-cofiber f))
```

### The cofibers of the point inclusions in `B` are equivalent to `B`

```agda
module _
  {l : Level} {B : UU l} (b : B)
  where

  is-equiv-inl-cofiber-point : is-equiv (inl-cofiber (point b))
  is-equiv-inl-cofiber-point =
    is-equiv-universal-property-pushout'
      ( point b)
      ( terminal-map unit)
      ( cocone-pushout (point b) (terminal-map unit))
      ( is-equiv-is-contr (terminal-map unit) is-contr-unit is-contr-unit)
      ( up-pushout (point b) (terminal-map unit))

  compute-cofiber-point : B ≃ cofiber (point b)
  compute-cofiber-point = (inl-cofiber (point b) , is-equiv-inl-cofiber-point)
```

## See also

- Cofibers of maps are formally dual to
  [fibers of maps](foundation-core.fibers-of-maps.md)
