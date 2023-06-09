# The dependent universal property of pushouts

```agda
module synthetic-homotopy-theory.dependent-universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
```

</summary>

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
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
dependent-universal-property-pushout l f g {X} c =
  (P : X → UU l) → is-equiv (dependent-cocone-map f g c P)
```

## Properties

### Sections defined by the dependent universal property are unique up to homotopy

```agda
abstract
  uniqueness-dependent-universal-property-pushout :
    { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
    ( f : S → A) (g : S → B) (c : cocone f g X)
    ( dup-c : dependent-universal-property-pushout l f g c) →
    ( P : X → UU l) ( h : dependent-cocone f g c P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ k →
            htpy-dependent-cocone f g c P (dependent-cocone-map f g c P k) h))
  uniqueness-dependent-universal-property-pushout f g c dup-c P h =
    is-contr-is-equiv'
      ( fib (dependent-cocone-map f g c P) h)
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
