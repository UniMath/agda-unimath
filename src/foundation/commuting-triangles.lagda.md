---
title: Commuting triangles
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.commuting-triangles where

open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
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
     W
```

is said to commute if there is a homotopy between the map on the left and the composite map.

## Definition

```agda
module _ {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} where

  coherence-triangle :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle left right top = left ~ (right ∘ top)

  coherence-triangle' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle' left right top = (right ∘ top) ~ left
```

## Properties

### Top map is an equivalence

If the top map is an equivalence, then there is an equivalence between the coherence triangle with the map of the equivalence as with the inverse map of the equivalence.

```agda
module _ {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (e : A ≃ B) where

  equiv-coherence-triangle-inv-top :
    coherence-triangle left right (map-equiv e) ≃
    coherence-triangle' right left (map-inv-equiv e)
  equiv-coherence-triangle-inv-top =
    equiv-Π
      (λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a → equiv-concat (ap left (isretr-map-inv-equiv e a)) (right (map-equiv e a)))
```
