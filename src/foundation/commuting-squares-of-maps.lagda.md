# Commuting squares of maps

```agda
module foundation.commuting-squares-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.commuting-squares-of-maps public

open import foundation.equivalences

open import foundation-core.identity-types
open import foundation-core.universe-levels
```

</details>

## Composing and inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both equivalences, then the square remains commuting if we invert those equivalences.

```agda
coherence-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square-maps (map-equiv top) left right (map-equiv bottom) →
  coherence-square-maps (map-inv-equiv top) right left (map-inv-equiv bottom)
coherence-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv' bottom
    ( ( ap right (inv (issec-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

coherence-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square-maps top (map-equiv left) (map-equiv right) bottom →
  coherence-square-maps bottom (map-inv-equiv left) (map-inv-equiv right) top
coherence-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv right
    ( inv (H (map-inv-equiv left x)) ∙ ap bottom (issec-map-inv-equiv left x))
```
