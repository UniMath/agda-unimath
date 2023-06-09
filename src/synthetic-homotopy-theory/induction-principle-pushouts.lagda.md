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

## Definition

### The induction principle of pushouts

```agda
Ind-pushout :
  { l1 l2 l3 l4 : Level} (l : Level) →
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
Ind-pushout l {X = X} f g c =
  (P : X → UU l) → sec (dependent-cocone-map f g c P)

module _
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (ind-c : Ind-pushout l f g c)
  ( P : X → UU l)
  where

  ind-pushout : dependent-cocone f g c P → (x : X) → P x
  ind-pushout = pr1 (ind-c P)

  compute-ind-pushout :
    (h : dependent-cocone f g c P) →
    htpy-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-pushout h))
      ( h)
  compute-ind-pushout h =
    htpy-eq-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-pushout h))
      ( h)
      ( pr2 (ind-c P) h)

  left-compute-ind-pushout :
    ( h : dependent-cocone f g c P) (a : A) →
    ind-pushout h (horizontal-map-cocone f g c a) ＝
    horizontal-map-dependent-cocone f g c P h a
  left-compute-ind-pushout h = pr1 (compute-ind-pushout h)

  right-compute-ind-pushout :
    ( h : dependent-cocone f g c P) (b : B) →
    ind-pushout h (vertical-map-cocone f g c b) ＝
    vertical-map-dependent-cocone f g c P h b
  right-compute-ind-pushout h =
    pr1 (pr2 (compute-ind-pushout h))

  path-compute-ind-pushout :
    (h : dependent-cocone f g c P) →
    coherence-htpy-dependent-cocone f g c P
      ( dependent-cocone-map f g c P (ind-pushout h))
      ( h)
      ( left-compute-ind-pushout h)
      ( right-compute-ind-pushout h)
  path-compute-ind-pushout h =
    pr2 (pr2 (compute-ind-pushout h))
```
