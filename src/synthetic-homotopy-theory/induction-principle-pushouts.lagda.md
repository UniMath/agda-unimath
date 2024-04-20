# The induction principle of pushouts

```agda
module synthetic-homotopy-theory.induction-principle-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sections
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
  dependent-cocone-map f g c P : ((x : X) → P x) → dependent-cocone f g c P
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
  { l1 l2 l3 l4 : Level} (l : Level) →
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
induction-principle-pushout l {X = X} f g c =
  (P : X → UU l) → section (dependent-cocone-map f g c P)

module _
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( ind-c : induction-principle-pushout l f g c)
  ( P : X → UU l)
  where

  ind-induction-principle-pushout : dependent-cocone f g c P → (x : X) → P x
  ind-induction-principle-pushout = pr1 (ind-c P)

  eq-compute-ind-induction-principle-pushout :
    (h : dependent-cocone f g c P) →
    dependent-cocone-map f g c P (ind-induction-principle-pushout h) ＝ h
  eq-compute-ind-induction-principle-pushout = pr2 (ind-c P)

  compute-ind-induction-principle-pushout :
    (h : dependent-cocone f g c P) →
    htpy-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-induction-principle-pushout h))
      ( h)
  compute-ind-induction-principle-pushout h =
    htpy-eq-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-induction-principle-pushout h))
      ( h)
      ( eq-compute-ind-induction-principle-pushout h)

  compute-horizontal-map-ind-induction-principle-pushout :
    ( h : dependent-cocone f g c P) (a : A) →
    ind-induction-principle-pushout h (horizontal-map-cocone f g c a) ＝
    horizontal-map-dependent-cocone f g c P h a
  compute-horizontal-map-ind-induction-principle-pushout h =
    pr1 (compute-ind-induction-principle-pushout h)

  compute-vertical-map-ind-induction-principle-pushout :
    ( h : dependent-cocone f g c P) (b : B) →
    ind-induction-principle-pushout h (vertical-map-cocone f g c b) ＝
    vertical-map-dependent-cocone f g c P h b
  compute-vertical-map-ind-induction-principle-pushout h =
    pr1 (pr2 (compute-ind-induction-principle-pushout h))

  compute-glue-ind-induction-principle-pushout :
    (h : dependent-cocone f g c P) →
    coherence-htpy-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-induction-principle-pushout h))
      ( h)
      ( compute-horizontal-map-ind-induction-principle-pushout h)
      ( compute-vertical-map-ind-induction-principle-pushout h)
  compute-glue-ind-induction-principle-pushout h =
    pr2 (pr2 (compute-ind-induction-principle-pushout h))
```
