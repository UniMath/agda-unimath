# Pushouts

```agda
module synthetic-homotopy-theory.pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

The {{#concept "standard pushout"}} `A ⊔_𝒮 B` of `𝒮` is a postulated choice of a
type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) of
`𝒮` with codomain `X` satisfying the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
of `𝒮`. In other words, the standard pushout `A ⊔_𝒮 B` of `𝒮` comes equipped
with a cocone structure `(inl , inr , glue)` where

```text
          g
    S --------> B
    |           |
  f |   glue    | inr
    V           V
    A ------> A ⊔_𝒮 B,
        inl
```

such that for any type `Y`, the
[evaluation map](synthetic-homotopy-theory.operations-cocones-under-span-diagrams.md)

```text
  (A ⊔_𝒮 B → Y) → cocone 𝒮 Y
```

is an [equivalence](foundation-core.equivalences.md).

## Postulates

We will assume that for any span diagram

```text
      f     g
  A <--- S ---> B,
```

where `S : UU l1`, `A : UU l2`, and `B : UU l3` there is a pushout in
`UU (l1 ⊔ l2 ⊔ l3)`.

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  postulate
    standard-pushout : UU (l1 ⊔ l2 ⊔ l3)

  postulate
    inl-standard-pushout : domain-span-diagram 𝒮 → standard-pushout

  postulate
    inr-standard-pushout : codomain-span-diagram 𝒮 → standard-pushout

  postulate
    glue-standard-pushout :
      coherence-square-maps
        ( right-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒮)
        ( inr-standard-pushout)
        ( inl-standard-pushout)

  cocone-standard-pushout :
    cocone-span-diagram 𝒮 standard-pushout
  pr1 cocone-standard-pushout = inl-standard-pushout
  pr1 (pr2 cocone-standard-pushout) = inr-standard-pushout
  pr2 (pr2 cocone-standard-pushout) = glue-standard-pushout

  postulate
    universal-property-pushout-standard-pushout :
      universal-property-pushout 𝒮 cocone-standard-pushout

  equiv-universal-property-pushout-standard-pushout :
    {l4 : Level} (X : UU l4) → (standard-pushout → X) ≃ cocone-span-diagram 𝒮 X
  pr1 (equiv-universal-property-pushout-standard-pushout X) =
    cocone-map-span-diagram 𝒮 cocone-standard-pushout
  pr2 (equiv-universal-property-pushout-standard-pushout X) =
    universal-property-pushout-standard-pushout X
```

## Definitions

### The cogap map

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  cogap-cocone-span-diagram : cocone-span-diagram 𝒮 X → standard-pushout 𝒮 → X
  cogap-cocone-span-diagram =
    map-inv-equiv (equiv-universal-property-pushout-standard-pushout 𝒮 X)

  is-section-cogap-cocone-span-diagram :
    is-section
      ( cocone-map-span-diagram 𝒮 (cocone-standard-pushout 𝒮))
      ( cogap-cocone-span-diagram)
  is-section-cogap-cocone-span-diagram =
    is-section-map-inv-equiv
      ( equiv-universal-property-pushout-standard-pushout 𝒮 X)

  is-retraction-cogap-cocone-span-diagram :
    is-retraction
      ( cocone-map-span-diagram 𝒮 (cocone-standard-pushout 𝒮))
      ( cogap-cocone-span-diagram)
  is-retraction-cogap-cocone-span-diagram =
    is-retraction-map-inv-equiv
      ( equiv-universal-property-pushout-standard-pushout 𝒮 X)
```

### The small predicate on cocones under span diagrams of being a pushout cocone

The `is-pushout` predicate defined below is a
[small type](foundation.small-types.md), as opposed to the universal property of
pushouts, which is in `UUω`.

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  is-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pushout = is-equiv (cogap-cocone-span-diagram 𝒮 c)

  is-prop-is-pushout : is-prop is-pushout
  is-prop-is-pushout = is-property-is-equiv (cogap-cocone-span-diagram 𝒮 c)

  is-pushout-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-pushout-Prop = is-pushout
  pr2 is-pushout-Prop = is-prop-is-pushout
```

## Properties

### Standard pushouts satisfy the universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  universal-property-pushout-is-pushout :
    is-pushout 𝒮 c → universal-property-pushout 𝒮 c
  universal-property-pushout-is-pushout H =
    universal-property-pushout-universal-property-pushout-is-equiv 𝒮
      ( cocone-standard-pushout 𝒮)
      ( c)
      ( cogap-cocone-span-diagram 𝒮 c)
      ( htpy-cocone-universal-property-pushout 𝒮
        ( cocone-standard-pushout 𝒮)
        ( universal-property-pushout-standard-pushout 𝒮)
        ( c))
      ( H)
      ( universal-property-pushout-standard-pushout 𝒮)

  is-pushout-universal-property-pushout :
    universal-property-pushout 𝒮 c → is-pushout 𝒮 c
  is-pushout-universal-property-pushout =
    is-equiv-universal-property-pushout-universal-property-pushout 𝒮
      ( cocone-standard-pushout 𝒮)
      ( c)
      ( cogap-cocone-span-diagram 𝒮 c)
      ( htpy-cocone-universal-property-pushout 𝒮
        ( cocone-standard-pushout 𝒮)
        ( universal-property-pushout-standard-pushout 𝒮)
        ( c))
      ( universal-property-pushout-standard-pushout 𝒮)
```

### Standard pushouts satisfy the dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  dependent-universal-property-pushout-standard-pushout :
    dependent-universal-property-pushout 𝒮 (cocone-standard-pushout 𝒮)
  dependent-universal-property-pushout-standard-pushout =
    dependent-universal-property-universal-property-pushout
      ( 𝒮)
      ( cocone-standard-pushout 𝒮)
      ( universal-property-pushout-standard-pushout 𝒮)

  equiv-dependent-universal-property-pushout :
    (P : standard-pushout 𝒮 → UU l4) →
    ((x : standard-pushout 𝒮) → P x) ≃
    dependent-cocone-span-diagram 𝒮 (cocone-standard-pushout 𝒮) P
  pr1 (equiv-dependent-universal-property-pushout P) =
    dependent-cocone-map-span-diagram 𝒮 (cocone-standard-pushout 𝒮) P
  pr2 (equiv-dependent-universal-property-pushout P) =
    dependent-universal-property-pushout-standard-pushout P
```

### Computation with the cogap map

```agda
module _
  { l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  compute-inl-cogap-cocone-span-diagram :
    ( a : domain-span-diagram 𝒮) →
    cogap-cocone-span-diagram 𝒮 c (inl-standard-pushout 𝒮 a) ＝
    left-map-cocone-span-diagram 𝒮 c a
  compute-inl-cogap-cocone-span-diagram =
    left-htpy-cocone-universal-property-pushout
      ( 𝒮)
      ( cocone-standard-pushout 𝒮)
      ( universal-property-pushout-standard-pushout 𝒮)
      ( c)

  compute-inr-cogap-cocone-span-diagram :
    ( b : codomain-span-diagram 𝒮) →
    cogap-cocone-span-diagram 𝒮 c (inr-standard-pushout 𝒮 b) ＝
    right-map-cocone-span-diagram 𝒮 c b
  compute-inr-cogap-cocone-span-diagram =
    right-htpy-cocone-universal-property-pushout
      ( 𝒮)
      ( cocone-standard-pushout 𝒮)
      ( universal-property-pushout-standard-pushout 𝒮)
      ( c)

  compute-glue-cogap-cocone-span-diagram :
    statement-coherence-htpy-cocone-span-diagram 𝒮
      ( cocone-map-span-diagram 𝒮
        ( cocone-standard-pushout 𝒮)
        ( cogap-cocone-span-diagram 𝒮 c))
      ( c)
      ( compute-inl-cogap-cocone-span-diagram)
      ( compute-inr-cogap-cocone-span-diagram)
  compute-glue-cogap-cocone-span-diagram =
    coherence-htpy-cocone-universal-property-pushout
      ( 𝒮)
      ( cocone-standard-pushout 𝒮)
      ( universal-property-pushout-standard-pushout 𝒮)
      ( c)
```
