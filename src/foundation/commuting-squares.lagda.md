#  Commuting squares

```agda
module foundation.commuting-squares where

open import foundation-core.commuting-squares public

open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation.equivalences
```

## Composing and inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both equivalences, then the square remains commuting if we invert those equivalences.

```agda
commuting-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  commuting-square (map-equiv top) left right (map-equiv bottom) →
  commuting-square (map-inv-equiv top) right left (map-inv-equiv bottom)
commuting-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv' bottom
    ( ( ap right (inv (issec-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

commuting-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  commuting-square top (map-equiv left) (map-equiv right) bottom →
  commuting-square bottom (map-inv-equiv left) (map-inv-equiv right) top
commuting-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv right
    ( inv (H (map-inv-equiv left x)) ∙ ap bottom (issec-map-inv-equiv left x))
```
