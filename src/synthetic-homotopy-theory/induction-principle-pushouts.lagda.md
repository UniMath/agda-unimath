# The induction principle of pushouts

```agda
module synthetic-homotopy-theory.induction-principle-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sections
open import foundation.spans
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
```

</details>

## Idea

The **induction principle of pushouts** asserts that for every
[dependent cocone](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
of a type family `P` over a type `X` equipped with a
[cocone](synthetic-homotopy-theory.cocones-under-spans.md) `c` there is a
section of `P` corresponding to `c`. More precisely, it asserts that the map

```text
  dependent-cocone-span-map f g c P : ((x : X) → P x) → dependent-cocone-span f g c P
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
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} (c : cocone-span s X) →
  UUω
induction-principle-pushout s {X} c =
  {l : Level} (P : X → UU l) → section (dependent-cocone-span-map s c P)

module _
  {l1 l2 l3 l4 l : Level} (s : span l1 l2 l3) {X : UU l4}
  (c : cocone-span s X)
  (ind-c : induction-principle-pushout s c)
  (P : X → UU l)
  where

  ind-induction-principle-pushout : dependent-cocone-span s c P → (x : X) → P x
  ind-induction-principle-pushout = pr1 (ind-c P)

  compute-ind-induction-principle-pushout :
    (h : dependent-cocone-span s c P) →
    htpy-dependent-cocone-span s c P
      ( dependent-cocone-span-map s c P (ind-induction-principle-pushout h))
      ( h)
  compute-ind-induction-principle-pushout h =
    htpy-eq-dependent-cocone-span s c P
      ( dependent-cocone-span-map s c P (ind-induction-principle-pushout h))
      ( h)
      ( pr2 (ind-c P) h)

  left-compute-ind-induction-principle-pushout :
    ( h : dependent-cocone-span s c P) (a : domain-span s) →
    ind-induction-principle-pushout h (horizontal-map-cocone-span s c a) ＝
    horizontal-map-dependent-cocone-span s c P h a
  left-compute-ind-induction-principle-pushout h =
    pr1 (compute-ind-induction-principle-pushout h)

  right-compute-ind-induction-principle-pushout :
    ( h : dependent-cocone-span s c P) (b : codomain-span s) →
    ind-induction-principle-pushout h (vertical-map-cocone-span s c b) ＝
    vertical-map-dependent-cocone-span s c P h b
  right-compute-ind-induction-principle-pushout h =
    pr1 (pr2 (compute-ind-induction-principle-pushout h))

  path-compute-ind-induction-principle-pushout :
    (h : dependent-cocone-span s c P) →
    coherence-htpy-dependent-cocone-span s c P
      ( dependent-cocone-span-map s c P (ind-induction-principle-pushout h))
      ( h)
      ( left-compute-ind-induction-principle-pushout h)
      ( right-compute-ind-induction-principle-pushout h)
  path-compute-ind-induction-principle-pushout h =
    pr2 (pr2 (compute-ind-induction-principle-pushout h))
```
