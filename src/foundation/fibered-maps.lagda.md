---
title: Maps fibered over a map
---

```agda
module foundation.fibered-maps where

open import foundation-core.commuting-squares
open import foundation-core.small-types
open import foundation-core.truncation-levels
open import foundation-core.truncated-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation.function-extensionality
open import foundation.slice
```

## Idea

Consider a diagram of the form

```md
  A         B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y
       i
```

A fibered map from `f` to `g` over `i` is a map `h : A → B` such that the square `(i ∘ f) ~ (g ∘ h)` commutes.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-fibered-map : 
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) → UU (l1 ⊔ l4)
  is-fibered-map f g i h = (i ∘ f) ~ (g ∘ h)

  hom-over :
    (f : A → X) (g : B → Y) (i : X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  hom-over f g i = Σ (A → B) (is-fibered-map f g i)

  fibered-map :
    (f : A → X) (g : B → Y) → UU (l1 ⊔ l3 ⊔ l2 ⊔ l4)
  fibered-map f g = Σ (X → Y) (hom-over f g)

  fiberwise-hom-over :
    (f : A → X) (g : B → Y) (i : X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-hom-over f g i = (x : X) → fib f x → fib g (i x)
```

## Properties

### Fibered maps and fiberwise maps over are equivalent

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  fiberwise-hom-over-hom-over :
    hom-over f g i → fiberwise-hom-over f g i
  fiberwise-hom-over-hom-over (pair h H) .(f a) (pair a refl) =
    pair (h a) (inv (H a))

  hom-over-fiberwise-hom-over :
    fiberwise-hom-over f g i → hom-over f g i
  pr1 (hom-over-fiberwise-hom-over α) a = pr1 (α (f a) (pair a refl))
  pr2 (hom-over-fiberwise-hom-over α) a = inv (pr2 (α (f a) (pair a refl)))

  issec-hom-over-fiberwise-hom-over-eq-htpy :
    (α : fiberwise-hom-over f g i) (x : X) →
    ( fiberwise-hom-over-hom-over
      ( hom-over-fiberwise-hom-over α) x) ~ (α x)
  issec-hom-over-fiberwise-hom-over-eq-htpy α .(f a) (pair a refl) =
    eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

  issec-hom-over-fiberwise-hom-over :
    ( ( fiberwise-hom-over-hom-over) ∘
      ( hom-over-fiberwise-hom-over)) ~ id
  issec-hom-over-fiberwise-hom-over α =
    eq-htpy
      ( eq-htpy ∘ issec-hom-over-fiberwise-hom-over-eq-htpy α)

  isretr-hom-over-fiberwise-hom-over :
    ( ( hom-over-fiberwise-hom-over) ∘
      ( fiberwise-hom-over-hom-over)) ~ id
  isretr-hom-over-fiberwise-hom-over (pair h H) =
    eq-pair-Σ refl (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-hom-over-hom-over :
      is-equiv (fiberwise-hom-over-hom-over)
    is-equiv-fiberwise-hom-over-hom-over =
      is-equiv-has-inverse
        ( hom-over-fiberwise-hom-over)
        ( issec-hom-over-fiberwise-hom-over)
        ( isretr-hom-over-fiberwise-hom-over)

  abstract
    is-equiv-hom-over-fiberwise-hom-over :
      is-equiv (hom-over-fiberwise-hom-over)
    is-equiv-hom-over-fiberwise-hom-over =
      is-equiv-has-inverse
        ( fiberwise-hom-over-hom-over)
        ( isretr-hom-over-fiberwise-hom-over)
        ( issec-hom-over-fiberwise-hom-over)

  equiv-fiberwise-hom-over-hom-over :
    hom-over f g i ≃ fiberwise-hom-over f g i 
  equiv-fiberwise-hom-over-hom-over = 
    pair
      ( fiberwise-hom-over-hom-over)
      ( is-equiv-fiberwise-hom-over-hom-over)

  equiv-hom-over-fiberwise-hom-over :
    fiberwise-hom-over f g i ≃ hom-over f g i
  equiv-hom-over-fiberwise-hom-over = 
    pair
      ( hom-over-fiberwise-hom-over)
      ( is-equiv-hom-over-fiberwise-hom-over)

  equiv-hom-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ hom-over f g i
  equiv-hom-over-fiberwise-hom =
    equiv-hom-slice-fiberwise-hom (i ∘ f) g

  equiv-fiberwise-hom-over-fiberwise-hom : 
    fiberwise-hom (i ∘ f) g ≃ fiberwise-hom-over f g i
  equiv-fiberwise-hom-over-fiberwise-hom =
    (equiv-fiberwise-hom-over-hom-over) ∘e (equiv-hom-over-fiberwise-hom)

  is-small-fiberwise-hom-over :
    is-small (l1 ⊔ l2 ⊔ l4) (fiberwise-hom-over f g i)
  is-small-fiberwise-hom-over =
    pair
      ( hom-over f g i)
      ( equiv-hom-over-fiberwise-hom-over)
```

### Fibered maps compose horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  {f : A → X} {g : B → Y} {h : C → Z}
  where

  is-fibered-map-comp-horizontal :
    {k : X → Y} {l : Y → Z} {i : A → B} {j : B → C} →
    is-fibered-map f g k i → is-fibered-map g h l j →
    is-fibered-map f h (l ∘ k) (j ∘ i)
  is-fibered-map-comp-horizontal {k} {l} {i} {j} =
    coherence-square-comp-horizontal i j f g h k l

  hom-over-comp-horizontal :
    {k : X → Y} {l : Y → Z} →
    hom-over f g k → hom-over g h l → hom-over f h (l ∘ k)
  hom-over-comp-horizontal {k} {l} (i , I) (j , J) =
    j ∘ i , is-fibered-map-comp-horizontal {k} {l} I J

  fibered-map-comp-horizontal :
    fibered-map f g → fibered-map g h → fibered-map f h
  fibered-map-comp-horizontal (k , iI) (l , jJ) =
    l ∘ k , hom-over-comp-horizontal {k} {l} iI jJ
```

### Fibered maps compose vertically

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4}
  {X : UU l5} {Y : UU l6}
  {i : A → B} {j : C → D} {k : X → Y}
  {f : A → C} {g : B → D}
  {f' : C → X} {g' : D → Y}
  where

  is-fibered-map-comp-vertical :
    is-fibered-map f g j i → is-fibered-map f' g' k j →
    is-fibered-map (f' ∘ f) (g' ∘ g) k i
  is-fibered-map-comp-vertical =
    coherence-square-comp-vertical i f g j f' g' k
```

### The truncation level of the type of fibered maps is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-is-fibered-map :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y →
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-trunc k (is-fibered-map f g i h)
  is-trunc-is-fibered-map k is-trunc-Y f g i h =
    is-trunc-Π k (λ x → is-trunc-Y (i (f x)) (g (h x)))

  is-trunc-hom-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y → is-trunc k B →
    (f : A → X) (g : B → Y) (i : X → Y) → is-trunc k (hom-over f g i)
  is-trunc-hom-over k is-trunc-Y is-trunc-B f g i =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( is-trunc-is-fibered-map k is-trunc-Y f g i)

  is-trunc-fibered-map :
    (k : 𝕋) → is-trunc k Y → is-trunc k B →
    (f : A → X) (g : B → Y) → is-trunc k (fibered-map f g)
  is-trunc-fibered-map k is-trunc-Y is-trunc-B f g =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-Y)
      ( is-trunc-hom-over k (is-trunc-succ-is-trunc k is-trunc-Y) is-trunc-B f g)
```

### The transpose of a fibered map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  transpose-is-fibered-map :
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-fibered-map f g i h → is-fibered-map h i g f
  transpose-is-fibered-map f g i h = inv-htpy

  transpose-hom-over :
    (f : A → X) (g : B → Y) (i : X → Y)
    ((h , H) : hom-over f g i) → hom-over h i g
  transpose-hom-over f g i (h , H) =
    f , transpose-is-fibered-map f g i h H

  transpose-fibered-map :
    (f : A → X) (g : B → Y)
    ((i , h , H) : fibered-map f g) → fibered-map h i
  transpose-fibered-map f g (i , hH) =
    g , transpose-hom-over f g i hH
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B)
  where

  is-fibered-over-self : is-fibered-map id id h h
  is-fibered-over-self = refl-htpy

  hom-over-self : hom-over id id h
  hom-over-self = pair h is-fibered-over-self

  fibered-map-self : fibered-map id id
  fibered-map-self = pair h hom-over-self

  is-fibered-id : is-fibered-map h h id id
  is-fibered-id = refl-htpy

  hom-over-id : hom-over h h id
  hom-over-id = pair id is-fibered-id

  fibered-map-id : fibered-map h h
  fibered-map-id = pair id hom-over-id
```
