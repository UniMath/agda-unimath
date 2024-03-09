# Morphisms of twisted pointed arrows

```agda
module structured-types.morphisms-twisted-pointed-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.morphisms-twisted-arrows
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

A
{{#concept "morphism of twisted pointed arrows" Agda=hom-twisted-pointed-arrow}}
from a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` to a pointed
map `g : X →∗ Y` is a [triple](foundation.dependent-pair-types.md) `(i , j , H)`
consisting of pointed maps `i : X →∗ A` and `j : B →∗ Y` and a
[pointed homotopy](structured-types.pointed-homotopies.md)
`H : j ∘∗ f ~∗ g ∘∗ i` witnessing that the diagram

```text
         i
    A <----- X
    |        |
  f |        | g
    V        V
    B -----> Y
        j
```

commutes.

## Definitions

### Morphisms of twisted pointed arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y)
  where

  coherence-hom-twisted-pointed-arrow :
    (X →∗ A) → (B →∗ Y) → UU (l3 ⊔ l4)
  coherence-hom-twisted-pointed-arrow i j = ((j ∘∗ f) ∘∗ i) ~∗ g

  hom-twisted-pointed-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-twisted-pointed-arrow =
    Σ (X →∗ A) (λ i → Σ (B →∗ Y) (coherence-hom-twisted-pointed-arrow i))

module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  {f : A →∗ B} {g : X →∗ Y} (h : hom-twisted-pointed-arrow f g)
  where

  pointed-map-domain-hom-twisted-pointed-arrow : X →∗ A
  pointed-map-domain-hom-twisted-pointed-arrow = pr1 h

  map-domain-hom-twisted-pointed-arrow :
    type-Pointed-Type X → type-Pointed-Type A
  map-domain-hom-twisted-pointed-arrow =
    map-pointed-map pointed-map-domain-hom-twisted-pointed-arrow

  preserves-point-map-domain-hom-twisted-pointed-arrow :
    map-domain-hom-twisted-pointed-arrow (point-Pointed-Type X) ＝
    point-Pointed-Type A
  preserves-point-map-domain-hom-twisted-pointed-arrow =
    preserves-point-pointed-map pointed-map-domain-hom-twisted-pointed-arrow

  pointed-map-codomain-hom-twisted-pointed-arrow : B →∗ Y
  pointed-map-codomain-hom-twisted-pointed-arrow = pr1 (pr2 h)

  map-codomain-hom-twisted-pointed-arrow :
    type-Pointed-Type B → type-Pointed-Type Y
  map-codomain-hom-twisted-pointed-arrow =
    map-pointed-map pointed-map-codomain-hom-twisted-pointed-arrow

  preserves-point-map-codomain-hom-twisted-pointed-arrow :
    map-codomain-hom-twisted-pointed-arrow (point-Pointed-Type B) ＝
    point-Pointed-Type Y
  preserves-point-map-codomain-hom-twisted-pointed-arrow =
    preserves-point-pointed-map
      ( pointed-map-codomain-hom-twisted-pointed-arrow)

  coh-hom-twisted-pointed-arrow :
    coherence-hom-twisted-pointed-arrow
      ( f)
      ( g)
      ( pointed-map-domain-hom-twisted-pointed-arrow)
      ( pointed-map-codomain-hom-twisted-pointed-arrow)
  coh-hom-twisted-pointed-arrow = pr2 (pr2 h)

  htpy-coh-hom-twisted-pointed-arrow :
    coherence-hom-twisted-arrow
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( map-domain-hom-twisted-pointed-arrow)
      ( map-codomain-hom-twisted-pointed-arrow)
  htpy-coh-hom-twisted-pointed-arrow =
    htpy-pointed-htpy coh-hom-twisted-pointed-arrow
```
