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

A fibered map from `f` to `g` over `i` is a map `h : A → B` such that the square commutes (`(i ∘ f) ~ (g ∘ h)`).


## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-fibered-map : 
    (i : X → Y) (f : A → X) (g : B → Y) (h : A → B) → UU (l1 ⊔ l4)
  is-fibered-map i f g h = (i ∘ f) ~ (g ∘ h)

  fibered-map :
    (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ l2 ⊔ l4)
  fibered-map i f g = Σ (A → B) (is-fibered-map i f g)

  hom-over :
    (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ l2 ⊔ l4)
  hom-over i f g = hom-slice (i ∘ f) g

  fiberwise-hom-over :
    (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-hom-over i f g = (x : X) → fib f x → fib g (i x)

  eq-hom-over-fibered-map : fibered-map ＝ hom-over
  eq-hom-over-fibered-map = refl

  eq-fibered-map-hom-over : hom-over ＝ fibered-map
  eq-fibered-map-hom-over = refl
```

## Properties

### Fibered maps and fiberwise maps over are equivalent

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y)
  where
  fiberwise-hom-over-hom-over :
    hom-over i f g → fiberwise-hom-over i f g
  fiberwise-hom-over-hom-over (pair h H) .(f a) (pair a refl) =
    pair (h a) (inv (H a))
  hom-over-fiberwise-hom-over :
    fiberwise-hom-over i f g → hom-over i f g
  pr1 (hom-over-fiberwise-hom-over α) a = pr1 (α (f a) (pair a refl))
  pr2 (hom-over-fiberwise-hom-over α) a = inv (pr2 (α (f a) (pair a refl)))
  issec-hom-over-fiberwise-hom-over-eq-htpy :
    (α : fiberwise-hom-over i f g) (x : X) →
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
    hom-over i f g ≃ fiberwise-hom-over i f g 
  equiv-fiberwise-hom-over-hom-over = 
    pair
      ( fiberwise-hom-over-hom-over)
      ( is-equiv-fiberwise-hom-over-hom-over)

  equiv-hom-over-fiberwise-hom-over :
    fiberwise-hom-over i f g ≃ hom-over i f g
  equiv-hom-over-fiberwise-hom-over = 
    pair
      ( hom-over-fiberwise-hom-over)
      ( is-equiv-hom-over-fiberwise-hom-over)

  equiv-hom-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ hom-over i f g
  equiv-hom-over-fiberwise-hom =
    equiv-hom-slice-fiberwise-hom (i ∘ f) g

  equiv-fiberwise-hom-over-fiberwise-hom : 
    fiberwise-hom (i ∘ f) g ≃ fiberwise-hom-over i f g
  equiv-fiberwise-hom-over-fiberwise-hom =
    (equiv-fiberwise-hom-over-hom-over) ∘e (equiv-hom-over-fiberwise-hom)

  is-small-fiberwise-hom-over :
    is-small (l1 ⊔ l2 ⊔ l4) (fiberwise-hom-over i f g)
  is-small-fiberwise-hom-over =
    pair
      ( hom-over i f g)
      ( equiv-hom-over-fiberwise-hom-over)
```

### Fibered maps compose horizontally and vertically

```agda
_∘fm_ :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  {i : A → B} {j : B → C}
  {f : A → X} {g : B → Y} {h : C → Z}
  {k : X → Y} {l : Y → Z}
  → is-fibered-map l g h j → is-fibered-map k f g i →
  is-fibered-map (l ∘ k) f h (j ∘ i)
_∘fm_ {i = i} {j} {f} {g} {h} {k} {l} J I =
  coherence-square-comp-horizontal i j f g h k l I J

_∙fm_ :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4}
  {X : UU l5} {Y : UU l6}
  {i : A → B} {j : C → D} {k : X → Y}
  {f : A → C} {g : B → D}
  {f' : C → X} {g' : D → Y}
  → is-fibered-map j f g i → is-fibered-map k f' g' j →
  is-fibered-map k (f' ∘ f) (g' ∘ g) i
_∙fm_ {i = i} {j} {k} {f} {g} {f'} {g'} I J =
  coherence-square-comp-vertical i f g j f' g' k I J
```

### The truncation level of the type of fibered maps is determined by the codomains

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-is-fibered-map-is-trunc-codomain :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y →
    (i : X → Y) (f : A → X) (g : B → Y) (h : A → B) →
    is-trunc k (is-fibered-map i f g h)
  is-trunc-is-fibered-map-is-trunc-codomain k is-trunc-succ-Y i f g h =
    is-trunc-Π k (λ x → is-trunc-succ-Y (i (f x)) (g (h x)))

  is-trunc-fibered-map :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y → is-trunc k B →
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-trunc k (fibered-map i f g)
  is-trunc-fibered-map k is-trunc-succ-Y is-trunc-B i f g =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( is-trunc-is-fibered-map-is-trunc-codomain k is-trunc-succ-Y i f g)
```

## Examples

```agda
is-fibered-over-self :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B) → is-fibered-map h id id h
is-fibered-over-self h = refl-htpy

hom-over-self :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B) → hom-over h id id
hom-over-self h = pair h refl-htpy

is-fibered-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B) → is-fibered-map id h h id
is-fibered-id h = refl-htpy

hom-over-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B) → hom-over id h h
hom-over-id h = pair id refl-htpy

is-fibered-self-endo :
  {l : Level} {A : UU l}
  (h : A → A) → is-fibered-map h h h h
is-fibered-self-endo h = refl-htpy

hom-over-self-endo :
  {l : Level} {A : UU l}
  (h : A → A) → hom-over h h h
hom-over-self-endo h = pair h refl-htpy
```
