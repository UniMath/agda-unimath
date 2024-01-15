# The induction principle of pushouts

```agda
module synthetic-homotopy-theory.induction-principle-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sections
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
```

</details>

## Idea

The {{#concept "induction principle of pushouts"}} asserts that for every
[dependent cocone](synthetic-homotopy-theory.dependent-cocones-under-span-diagrams.md)
of a type family `P` over a type `X` equipped with a
[cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` there is
a section of `P` corresponding to `c`. More precisely, it asserts that the map

```text
  dependent-cocone-map-span-diagram f g c P :
    ((x : X) → P x) → dependent-cocone-span-diagram f g c P
```

has a [section](foundation.sections.md).

The fact that the induction principle of pushouts is
[logically equivalent](foundation.logical-equivalences.md) to the
[dependent universal property](synthetic-homotopy-theory.dependent-universal-property-pushouts.md)
of pushouts is shown in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).

## Definition

### The induction principle of pushouts

```agda
induction-principle-pushout :
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) → UUω
induction-principle-pushout 𝒮 {X} c =
  {l : Level} (P : X → UU l) → section (dependent-cocone-map-span-diagram 𝒮 c P)

module _
  {l1 l2 l3 l4 l : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  (c : cocone-span-diagram 𝒮 X)
  (H : induction-principle-pushout 𝒮 c)
  (P : X → UU l)
  where

  ind-induction-principle-pushout :
    dependent-cocone-span-diagram 𝒮 c P → (x : X) → P x
  ind-induction-principle-pushout = pr1 (H P)

  eq-compute-ind-induction-principle-pushout :
    (h : dependent-cocone-span-diagram 𝒮 c P) →
    dependent-cocone-map-span-diagram 𝒮 c P
      ( ind-induction-principle-pushout h) ＝
    h
  eq-compute-ind-induction-principle-pushout h =
    pr2 (H P) h

  compute-ind-induction-principle-pushout :
    (h : dependent-cocone-span-diagram 𝒮 c P) →
    htpy-dependent-cocone-span-diagram 𝒮 c P
      ( dependent-cocone-map-span-diagram 𝒮 c P
        ( ind-induction-principle-pushout h))
      ( h)
  compute-ind-induction-principle-pushout h =
    htpy-eq-dependent-cocone-span-diagram 𝒮 c P
      ( dependent-cocone-map-span-diagram 𝒮 c P
        ( ind-induction-principle-pushout h))
      ( h)
      ( eq-compute-ind-induction-principle-pushout h)

  left-compute-ind-induction-principle-pushout :
    ( h : dependent-cocone-span-diagram 𝒮 c P) (a : domain-span-diagram 𝒮) →
    ind-induction-principle-pushout h
      ( left-map-cocone-span-diagram 𝒮 c a) ＝
    left-map-dependent-cocone-span-diagram 𝒮 c P h a
  left-compute-ind-induction-principle-pushout h =
    pr1 (compute-ind-induction-principle-pushout h)

  right-compute-ind-induction-principle-pushout :
    ( h : dependent-cocone-span-diagram 𝒮 c P) (b : codomain-span-diagram 𝒮) →
    ind-induction-principle-pushout h
      ( right-map-cocone-span-diagram 𝒮 c b) ＝
    right-map-dependent-cocone-span-diagram 𝒮 c P h b
  right-compute-ind-induction-principle-pushout h =
    pr1 (pr2 (compute-ind-induction-principle-pushout h))

  path-compute-ind-induction-principle-pushout :
    (h : dependent-cocone-span-diagram 𝒮 c P) →
    coherence-htpy-dependent-cocone-span-diagram 𝒮 c P
      ( dependent-cocone-map-span-diagram 𝒮 c P
        ( ind-induction-principle-pushout h))
      ( h)
      ( left-compute-ind-induction-principle-pushout h)
      ( right-compute-ind-induction-principle-pushout h)
  path-compute-ind-induction-principle-pushout h =
    pr2 (pr2 (compute-ind-induction-principle-pushout h))
```
