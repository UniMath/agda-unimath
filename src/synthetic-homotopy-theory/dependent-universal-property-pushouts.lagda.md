# The dependent universal property of pushouts

```agda
module synthetic-homotopy-theory.dependent-universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **dependent universal property of pushouts** asserts that every section of a
type family over a [pushout](synthetic-homotopy-theory.pushouts.md) corresponds
in a canonical way uniquely to a
[dependent cocone](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
over the [cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) on
the pushout.

## Definition

### The dependent universal property of pushouts

```agda
dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UUω
dependent-universal-property-pushout f g {X} c =
  {l : Level} (P : X → UU l) → is-equiv (dependent-cocone-map f g c P)
```

## Properties

### Sections defined by the dependent universal property are unique up to homotopy

```agda
abstract
  uniqueness-dependent-universal-property-pushout :
    { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
    ( f : S → A) (g : S → B) (c : cocone f g X)
    ( dup-c : dependent-universal-property-pushout f g c) →
    {l : Level} (P : X → UU l) ( h : dependent-cocone f g c P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ k →
            htpy-dependent-cocone f g c P (dependent-cocone-map f g c P k) h))
  uniqueness-dependent-universal-property-pushout f g c dup-c P h =
    is-contr-is-equiv'
      ( fiber (dependent-cocone-map f g c P) h)
      ( tot
        ( λ k →
          htpy-eq-dependent-cocone f g c P (dependent-cocone-map f g c P k) h))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ k →
          is-equiv-htpy-eq-dependent-cocone f g c P
            ( dependent-cocone-map f g c P k)
            ( h)))
      ( is-contr-map-is-equiv (dup-c P) h)
```

### The induction principle of pushouts is equivalent to the dependent universal property of pushouts

#### The induction principle of pushouts implies the dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  htpy-eq-dependent-cocone-map :
    induction-principle-pushout f g c →
    { l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
    dependent-cocone-map f g c P h ＝ dependent-cocone-map f g c P h' → h ~ h'
  htpy-eq-dependent-cocone-map ind-c {P = P} h h' p =
    ind-induction-principle-pushout f g c ind-c
      ( λ x → h x ＝ h' x)
      ( ( horizontal-htpy-eq-dependent-cocone f g c P
          ( dependent-cocone-map f g c P h)
          ( dependent-cocone-map f g c P h')
          ( p)) ,
        ( vertical-htpy-eq-dependent-cocone f g c P
          ( dependent-cocone-map f g c P h)
          ( dependent-cocone-map f g c P h')
          ( p)) ,
        ( λ s →
          map-compute-dependent-identification-eq-value h h'
            ( coherence-square-cocone f g c s)
            ( horizontal-htpy-eq-dependent-cocone f g c P
              ( dependent-cocone-map f g c P h)
              ( dependent-cocone-map f g c P h')
              ( p)
              ( f s))
            ( vertical-htpy-eq-dependent-cocone f g c P
              ( dependent-cocone-map f g c P h)
              ( dependent-cocone-map f g c P h')
              ( p)
              ( g s))
            ( coherence-square-htpy-eq-dependent-cocone f g c P
              ( dependent-cocone-map f g c P h)
              ( dependent-cocone-map f g c P h')
              ( p)
              ( s))))

  is-retraction-ind-induction-principle-pushout :
    (H : induction-principle-pushout f g c) →
    {l : Level} (P : X → UU l) →
    is-retraction
      ( dependent-cocone-map f g c P)
      ( ind-induction-principle-pushout f g c H P)
  is-retraction-ind-induction-principle-pushout ind-c P h =
    eq-htpy
      ( htpy-eq-dependent-cocone-map
        ( ind-c)
        ( ind-induction-principle-pushout f g c
          ( ind-c)
          ( P)
          ( dependent-cocone-map f g c P h))
        ( h)
        ( eq-compute-ind-induction-principle-pushout f g c ind-c P
          ( dependent-cocone-map f g c P h)))

  dependent-universal-property-pushout-induction-principle-pushout :
    induction-principle-pushout f g c →
    dependent-universal-property-pushout f g c
  dependent-universal-property-pushout-induction-principle-pushout ind-c P =
    is-equiv-is-invertible
      ( ind-induction-principle-pushout f g c ind-c P)
      ( eq-compute-ind-induction-principle-pushout f g c ind-c P)
      ( is-retraction-ind-induction-principle-pushout ind-c P)
```

#### The dependent universal property of pushouts implies the induction principle of pushouts

```agda
induction-principle-pushout-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-universal-property-pushout f g c →
  induction-principle-pushout f g c
induction-principle-pushout-dependent-universal-property-pushout
  f g c dup-c P = pr1 (dup-c P)
```

### The dependent pullback property of pushouts is equivalent to the dependent universal property of pushouts

#### The dependent universal property of pushouts implies the dependent pullback property of pushouts

```agda
triangle-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  ( dependent-cocone-map f g c P) ~
  ( ( tot (λ h → tot (λ h' → htpy-eq))) ∘
    ( gap
      ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
      ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
      ( cone-dependent-pullback-property-pushout f g c P)))
triangle-dependent-pullback-property-pushout f g (pair i (pair j H)) P h =
  eq-pair-eq-fiber (eq-pair-eq-fiber (inv (is-section-eq-htpy (apd h ∘ H))))

dependent-pullback-property-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-universal-property-pushout f g c →
  dependent-pullback-property-pushout f g c
dependent-pullback-property-dependent-universal-property-pushout
  f g (pair i (pair j H)) I P =
  let c = (pair i (pair j H)) in
  is-equiv-top-map-triangle
    ( dependent-cocone-map f g c P)
    ( tot (λ h → tot (λ h' → htpy-eq)))
    ( gap
      ( λ h x → tr P (H x) (h (f x)))
      ( _∘ g)
      ( cone-dependent-pullback-property-pushout f g c P))
    ( triangle-dependent-pullback-property-pushout f g c P)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h →
        is-equiv-tot-is-fiberwise-equiv
          ( λ h' → funext (λ x → tr P (H x) (h (f x))) (h' ∘ g))))
    ( I P)
```

#### The dependent pullback property of pushouts implies the dependent universal property of pushouts

```agda
dependent-universal-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-pullback-property-pushout f g c →
  dependent-universal-property-pushout f g c
dependent-universal-property-dependent-pullback-property-pushout
  f g (pair i (pair j H)) dpullback-c P =
  let c = (pair i (pair j H)) in
  is-equiv-left-map-triangle
    ( dependent-cocone-map f g c P)
    ( tot (λ h → tot (λ h' → htpy-eq)))
    ( gap
      ( λ h x → tr P (H x) (h (f x)))
      ( _∘ g)
      ( cone-dependent-pullback-property-pushout f g c P))
    ( triangle-dependent-pullback-property-pushout f g c P)
    ( dpullback-c P)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h →
        is-equiv-tot-is-fiberwise-equiv
          ( λ h' → funext (λ x → tr P (H x) (h (f x))) (h' ∘ g))))
```

### The nondependent and dependent universal property of pushouts are logically equivalent

This follows from the fact that the
[dependent pullback property of pushouts](synthetic-homotopy-theory.dependent-pullback-property-pushouts.md)
is logically equivalent to the
[pullback property of pushouts](synthetic-homotopy-theory.pullback-property-pushouts.md).

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X)
  where

  abstract
    universal-property-dependent-universal-property-pushout :
      dependent-universal-property-pushout f g c →
      universal-property-pushout f g c
    universal-property-dependent-universal-property-pushout dup-c {l} =
      universal-property-pushout-pullback-property-pushout f g c
        ( pullback-property-dependent-pullback-property-pushout f g c
          ( dependent-pullback-property-dependent-universal-property-pushout f g
            ( c)
            ( dup-c)))

    dependent-universal-property-universal-property-pushout :
      universal-property-pushout f g c →
      dependent-universal-property-pushout f g c
    dependent-universal-property-universal-property-pushout up-c =
      dependent-universal-property-dependent-pullback-property-pushout f g c
        ( dependent-pullback-property-pullback-property-pushout f g c
          ( pullback-property-pushout-universal-property-pushout f g c up-c))
```
