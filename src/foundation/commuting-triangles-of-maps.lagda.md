# Commuting triangles of maps

```agda
module foundation.commuting-triangles-of-maps where

open import foundation-core.commuting-triangles-of-maps public

open import foundation-core.equivalences
open import foundation-core.universe-levels

open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
```

## Idea

A triangle of maps

```md
 A ----> B
  \     /
   \   /
    V V
     X
```

is said to commute if there is a homotopy between the map on the left and the composite map.

## Properties

### Top map is an equivalence

If the top map is an equivalence, then there is an equivalence between the coherence triangle with the map of the equivalence as with the inverse map of the equivalence.

```agda
module _ {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (e : A ≃ B) where

  equiv-commuting-triangle-inv-top :
    commuting-triangle left right (map-equiv e) ≃
    commuting-triangle' right left (map-inv-equiv e)
  equiv-commuting-triangle-inv-top =
    equiv-Π
      (λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a → equiv-concat (ap left (isretr-map-inv-equiv e a)) (right (map-equiv e a)))
```
