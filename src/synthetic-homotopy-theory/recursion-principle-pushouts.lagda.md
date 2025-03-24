# The recursion principle of pushouts

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.recursion-principle-pushouts
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sections funext
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans funext
open import synthetic-homotopy-theory.dependent-cocones-under-spans funext univalence truncations
```

</details>

## Idea

The {{#concept "recursion principle of pushouts"}} asserts that for every type
`Y` and [cocone](synthetic-homotopy-theory.cocones-under-spans.md) on a type
`X`, the cocone map

```text
  cocone-map f g c Y : (X → Y) → cocone f g Y
```

has a [section](foundation.sections.md).

## Definition

### The recursion principle of pushouts

```agda
recursion-principle-pushout :
  { l1 l2 l3 l4 : Level} →
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  UUω
recursion-principle-pushout f g c =
  {l : Level} {Y : UU l} → section (cocone-map f g {Y = Y} c)

module _
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( rec-c : recursion-principle-pushout f g c)
  ( Y : UU l)
  where

  rec-recursion-principle-pushout : cocone f g Y → X → Y
  rec-recursion-principle-pushout = pr1 rec-c

  compute-rec-recursion-principle-pushout :
    (h : cocone f g Y) →
    htpy-cocone f g
      ( cocone-map f g c (rec-recursion-principle-pushout h))
      ( h)
  compute-rec-recursion-principle-pushout h =
    htpy-eq-cocone f g
      ( cocone-map f g c (rec-recursion-principle-pushout h))
      ( h)
      ( pr2 rec-c h)

  compute-horizontal-map-rec-recursion-principle-pushout :
    ( h : cocone f g Y) (a : A) →
    rec-recursion-principle-pushout h (horizontal-map-cocone f g c a) ＝
    horizontal-map-cocone f g h a
  compute-horizontal-map-rec-recursion-principle-pushout h =
    pr1 (compute-rec-recursion-principle-pushout h)

  compute-vertical-map-rec-recursion-principle-pushout :
    ( h : cocone f g Y) (b : B) →
    rec-recursion-principle-pushout h (vertical-map-cocone f g c b) ＝
    vertical-map-cocone f g h b
  compute-vertical-map-rec-recursion-principle-pushout h =
    pr1 (pr2 (compute-rec-recursion-principle-pushout h))

  compute-glue-rec-recursion-principle-pushout :
    (h : cocone f g Y) →
    statement-coherence-htpy-cocone f g
      ( cocone-map f g c (rec-recursion-principle-pushout h))
      ( h)
      ( compute-horizontal-map-rec-recursion-principle-pushout h)
      ( compute-vertical-map-rec-recursion-principle-pushout h)
  compute-glue-rec-recursion-principle-pushout h =
    pr2 (pr2 (compute-rec-recursion-principle-pushout h))
```
