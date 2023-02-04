---
title: Maps fibered over a map
---

```agda
module foundation.fibered-maps where

open import foundation-core.commuting-squares
open import foundation-core.cones-pullbacks
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
open import foundation-core.slice
open import foundation-core.universe-levels

open import foundation.function-extensionality
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
  (f : A → X) (g : B → Y)
  where

  is-map-over : (i : X → Y) (h : A → B) → UU (l1 ⊔ l4)
  is-map-over i h = (i ∘ f) ~ (g ∘ h)

  map-over : (i : X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  map-over i = Σ (A → B) (is-map-over i)

  fibered-map : UU (l1 ⊔ l3 ⊔ l2 ⊔ l4)
  fibered-map = Σ (X → Y) (map-over)

  fiberwise-map-over : (i : X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-map-over i = (x : X) → fib f x → fib g (i x)


  cone-fibered-map : ((i , h , H) : fibered-map) → cone i g A
  cone-fibered-map (i , h , H) = f , h , H
```

## Properties

### Fibered maps  and fiberwise maps over are equivalent notions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  fiberwise-map-over-map-over :
    map-over f g i → fiberwise-map-over f g i
  fiberwise-map-over-map-over (pair h H) .(f a) (pair a refl) =
    pair (h a) (inv (H a))

  map-over-fiberwise-map-over :
    fiberwise-map-over f g i → map-over f g i
  pr1 (map-over-fiberwise-map-over α) a = pr1 (α (f a) (pair a refl))
  pr2 (map-over-fiberwise-map-over α) a = inv (pr2 (α (f a) (pair a refl)))

  issec-map-over-fiberwise-map-over-eq-htpy :
    (α : fiberwise-map-over f g i) (x : X) →
    ( fiberwise-map-over-map-over
      ( map-over-fiberwise-map-over α) x) ~ (α x)
  issec-map-over-fiberwise-map-over-eq-htpy α .(f a) (pair a refl) =
    eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

  issec-map-over-fiberwise-map-over :
    ( ( fiberwise-map-over-map-over) ∘
      ( map-over-fiberwise-map-over)) ~ id
  issec-map-over-fiberwise-map-over α =
    eq-htpy
      ( eq-htpy ∘ issec-map-over-fiberwise-map-over-eq-htpy α)

  isretr-map-over-fiberwise-map-over :
    ( ( map-over-fiberwise-map-over) ∘
      ( fiberwise-map-over-map-over)) ~ id
  isretr-map-over-fiberwise-map-over (pair h H) =
    eq-pair-Σ refl (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-map-over-map-over :
      is-equiv (fiberwise-map-over-map-over)
    is-equiv-fiberwise-map-over-map-over =
      is-equiv-has-inverse
        ( map-over-fiberwise-map-over)
        ( issec-map-over-fiberwise-map-over)
        ( isretr-map-over-fiberwise-map-over)

  abstract
    is-equiv-map-over-fiberwise-map-over :
      is-equiv (map-over-fiberwise-map-over)
    is-equiv-map-over-fiberwise-map-over =
      is-equiv-has-inverse
        ( fiberwise-map-over-map-over)
        ( isretr-map-over-fiberwise-map-over)
        ( issec-map-over-fiberwise-map-over)

  equiv-fiberwise-map-over-map-over :
    map-over f g i ≃ fiberwise-map-over f g i
  equiv-fiberwise-map-over-map-over =
    pair
      ( fiberwise-map-over-map-over)
      ( is-equiv-fiberwise-map-over-map-over)

  equiv-map-over-fiberwise-map-over :
    fiberwise-map-over f g i ≃ map-over f g i
  equiv-map-over-fiberwise-map-over =
    pair
      ( map-over-fiberwise-map-over)
      ( is-equiv-map-over-fiberwise-map-over)

  equiv-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ map-over f g i
  equiv-map-over-fiberwise-hom =
    equiv-hom-slice-fiberwise-hom (i ∘ f) g

  equiv-fiberwise-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ fiberwise-map-over f g i
  equiv-fiberwise-map-over-fiberwise-hom =
    (equiv-fiberwise-map-over-map-over) ∘e (equiv-map-over-fiberwise-hom)

  is-small-fiberwise-map-over :
    is-small (l1 ⊔ l2 ⊔ l4) (fiberwise-map-over f g i)
  is-small-fiberwise-map-over =
    pair
      ( map-over f g i)
      ( equiv-map-over-fiberwise-map-over)
```

### Slice maps are equal to fibered maps over

```agda
eq-map-over-id-hom-slice :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g ＝ map-over f g id
eq-map-over-id-hom-slice f g = refl

eq-map-over-hom-slice :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y) → hom-slice (i ∘ f) g ＝ map-over f g i
eq-map-over-hom-slice f g i = refl
```

### Horizontal composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  {f : A → X} {g : B → Y} {h : C → Z}
  where

  is-map-over-comp-horizontal :
    {k : X → Y} {l : Y → Z} {i : A → B} {j : B → C} →
    is-map-over f g k i → is-map-over g h l j →
    is-map-over f h (l ∘ k) (j ∘ i)
  is-map-over-comp-horizontal {k} {l} {i} {j} =
    coherence-square-comp-horizontal i j f g h k l

  map-over-comp-horizontal :
    {k : X → Y} {l : Y → Z} →
    map-over f g k → map-over g h l → map-over f h (l ∘ k)
  map-over-comp-horizontal {k} {l} (i , I) (j , J) =
    j ∘ i , is-map-over-comp-horizontal {k} {l} I J

  fibered-map-comp-horizontal :
    fibered-map f g → fibered-map g h → fibered-map f h
  fibered-map-comp-horizontal (k , iI) (l , jJ) =
    l ∘ k , map-over-comp-horizontal {k} {l} iI jJ
```

### Vertical composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4}
  {X : UU l5} {Y : UU l6}
  {i : A → B} {j : C → D} {k : X → Y}
  where

  is-map-over-comp-vertical :
    {f : A → C} {g : B → D}
    {f' : C → X} {g' : D → Y} →
    is-map-over f g j i → is-map-over f' g' k j →
    is-map-over (f' ∘ f) (g' ∘ g) k i
  is-map-over-comp-vertical {f} {g} {f'} {g'} =
    coherence-square-comp-vertical i f g j f' g' k
```

### The truncation level of the types of fibered maps is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-is-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y →
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-trunc k (is-map-over f g i h)
  is-trunc-is-map-over k is-trunc-Y f g i h =
    is-trunc-Π k (λ x → is-trunc-Y (i (f x)) (g (h x)))

  is-trunc-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y → is-trunc k B →
    (f : A → X) (g : B → Y) (i : X → Y) → is-trunc k (map-over f g i)
  is-trunc-map-over k is-trunc-Y is-trunc-B f g i =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( is-trunc-is-map-over k is-trunc-Y f g i)

  is-trunc-fibered-map :
    (k : 𝕋) → is-trunc k Y → is-trunc k B →
    (f : A → X) (g : B → Y) → is-trunc k (fibered-map f g)
  is-trunc-fibered-map k is-trunc-Y is-trunc-B f g =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-Y)
      ( is-trunc-map-over k (is-trunc-succ-is-trunc k is-trunc-Y) is-trunc-B f g)
```

### The transpose of a fibered map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  transpose-is-map-over :
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-map-over f g i h → is-map-over h i g f
  transpose-is-map-over f g i h = inv-htpy

  transpose-map-over :
    (f : A → X) (g : B → Y) (i : X → Y)
    ((h , H) : map-over f g i) → map-over h i g
  transpose-map-over f g i (h , H) =
    f , transpose-is-map-over f g i h H

  transpose-fibered-map :
    (f : A → X) (g : B → Y)
    ((i , h , H) : fibered-map f g) → fibered-map h i
  transpose-fibered-map f g (i , hH) =
    g , transpose-map-over f g i hH
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B)
  where

  is-fibered-over-self : is-map-over id id h h
  is-fibered-over-self = refl-htpy

  map-over-self : map-over id id h
  map-over-self = pair h is-fibered-over-self

  fibered-map-self : fibered-map id id
  fibered-map-self = pair h map-over-self

  is-fibered-id : is-map-over h h id id
  is-fibered-id = refl-htpy

  map-over-id : map-over h h id
  map-over-id = pair id is-fibered-id

  fibered-map-id : fibered-map h h
  fibered-map-id = pair id map-over-id
```
