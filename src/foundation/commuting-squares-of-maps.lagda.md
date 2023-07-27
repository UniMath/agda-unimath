# Commuting squares of maps

```agda
module foundation.commuting-squares-of-maps where

open import foundation-core.commuting-squares-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.functoriality-function-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Properties

### Composing and inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both equivalences,
then the square remains commuting if we invert those equivalences.

```agda
coherence-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square-maps (map-equiv top) left right (map-equiv bottom) →
  coherence-square-maps (map-inv-equiv top) right left (map-inv-equiv bottom)
coherence-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv' bottom
    ( ( ap right (inv (is-section-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

coherence-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square-maps top (map-equiv left) (map-equiv right) bottom →
  coherence-square-maps bottom (map-inv-equiv left) (map-inv-equiv right) top
coherence-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv right
    ( ( inv (H (map-inv-equiv left x))) ∙
      ( ap bottom (is-section-map-inv-equiv left x)))

coherence-square-inv-all :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A ≃ X) (right : B ≃ Y) (bottom : X ≃ Y) →
  coherence-square-maps
    ( map-equiv top)
    ( map-equiv left)
    ( map-equiv right)
    ( map-equiv bottom) →
  coherence-square-maps
    ( map-inv-equiv bottom)
    ( map-inv-equiv right)
    ( map-inv-equiv left)
    ( map-inv-equiv top)
coherence-square-inv-all top left right bottom H =
  coherence-square-inv-vertical
    ( map-inv-equiv top)
    ( right)
    ( left)
    ( map-inv-equiv bottom)
    ( coherence-square-inv-horizontal
      ( top)
      ( map-equiv left)
      ( map-equiv right)
      ( bottom)
      ( H))
```

### Any commuting square of maps induces a commuting square of function spaces

```agda
precomp-coherence-square-maps :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D) →
  coherence-square-maps top left right bottom → (X : UU l5) →
  coherence-square-maps
    ( precomp right X)
    ( precomp bottom X)
    ( precomp top X)
    ( precomp left X)
precomp-coherence-square-maps top leeft right bottom H X =
  htpy-precomp H X
```
