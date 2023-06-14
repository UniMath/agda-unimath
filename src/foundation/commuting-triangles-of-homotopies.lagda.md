# Commuting triangles of homotopies

```agda
module foundation.commuting-triangles-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A triangle of homotopies of maps

```text
 f ----> g
  \     /
   \   /
    V V
     h
```

is said to commute if there is a homotopy between the homotopy on the left
`f ~ h` and the composite homotopy `f ~ g ~ h`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  where

  coherence-triangle-homotopies :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies left right top = left ~ (top ∙h right)

  coherence-triangle-homotopies' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies' left right top = (top ∙h right) ~ left
```

## Properties

### Distributive law for left whiskering

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {l3 : Level} {X : UU l3} (i : B → X)
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  distributivity-left-whisk :
    coherence-triangle-homotopies left right top →
    (i ·l left) ~ ((i ·l top) ∙h (i ·l right))
  distributivity-left-whisk T x =
    ap-concat-eq i (top x) (right x) (left x) (T x)
```

### Left whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  left-whisk-htpy-coherence-triangle-homotopies :
    {i : (x : A) → B x}
    (H : h ~ i) (T : coherence-triangle-homotopies left right top) →
    coherence-triangle-homotopies {h = i} (left ∙h H) (right ∙h H) top
  left-whisk-htpy-coherence-triangle-homotopies H T =
    (λ x → ap (_∙ H x) (T x)) ∙h assoc-htpy top right H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  left-whisk-coherence-triangle-homotopies :
    {l3 : Level} {X : UU l3} (i : B → X)
    (T : coherence-triangle-homotopies left right top) →
    coherence-triangle-homotopies
      {f = i ∘ f} {i ∘ g} {i ∘ h}
      (i ·l left) (i ·l right) (i ·l top)
  left-whisk-coherence-triangle-homotopies i =
    distributivity-left-whisk i left right top
```

### Right whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  right-whisk-htpy-coherence-triangle-homotopies :
    {i : (x : A) → B x}
    (T : coherence-triangle-homotopies left right top) (H : i ~ f) →
    coherence-triangle-homotopies {f = i} (H ∙h left) right (H ∙h top)
  right-whisk-htpy-coherence-triangle-homotopies T H =
    (λ x → ap (H x ∙_) (T x)) ∙h (inv-htpy-assoc-htpy H top right)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  right-whisk-coherence-triangle-homotopies :
    {l3 : Level} {X : UU l3}
    (T : coherence-triangle-homotopies left right top) (i : X → A) →
    coherence-triangle-homotopies
      {f = f ∘ i} {g ∘ i} {h ∘ i}
      (left ·r i) (right ·r i) (top ·r i)
  right-whisk-coherence-triangle-homotopies T i = T ∘ i
```
