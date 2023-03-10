# Commuting triangles of maps

```agda
module foundation.commuting-triangles-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.commuting-triangles-of-maps public

open import foundation.functoriality-dependent-function-types
open import foundation.identity-types

open import foundation-core.equivalences
open import foundation-core.universe-levels
```

</details>

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

  equiv-coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps' right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top =
    equiv-Π
      (λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a → equiv-concat (ap left (isretr-map-inv-equiv e a)) (right (map-equiv e a)))
```
