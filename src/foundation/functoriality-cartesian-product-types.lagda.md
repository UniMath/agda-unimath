---
title: Functoriality of cartesian product types
---

```agda
module foundation.functoriality-cartesian-product-types where

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map `map-prod : A × B → C × D`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-prod : (f : A → C) (g : B → D) → (A × B) → (C × D)
  pr1 (map-prod f g t) = f (pr1 t)
  pr2 (map-prod f g t) = g (pr2 t)

  map-prod-pr1 :
    (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
  map-prod-pr1 f g (pair a b) = refl

  map-prod-pr2 :
    (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
  map-prod-pr2 f g (pair a b) = refl
```

## Properties

### Functoriality of products preserves identity maps

```agda
map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl
```

### Functoriality of products preserves composition

```agda
map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k t = refl
```

### Functoriality of products preserves homotopies

```agda
htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)
```

### Functoriality of products preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  abstract
    is-equiv-map-prod :
      (f : A → C) (g : B → D) →
      is-equiv f → is-equiv g → is-equiv (map-prod f g)
    pr1
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod sf sg
    pr2
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp sf sg f g)) ∙h
      ( (htpy-map-prod Sf Sg) ∙h map-prod-id)
    pr1
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod rf rg
    pr2
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp f g rf rg)) ∙h
      ( (htpy-map-prod Rf Rg) ∙h map-prod-id)

  equiv-prod : (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
  pr1 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) = map-prod f g
  pr2 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) =
    is-equiv-map-prod f g is-equiv-f is-equiv-g
```

### The fibers of `map-prod f g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where
  
  map-compute-fib-map-prod :
    (t : C × D) → fib (map-prod f g) t → (fib f (pr1 t)) × (fib g (pr2 t))
  pr1
    ( pr1
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = a
  pr2
    ( pr1
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = refl
  pr1
    ( pr2
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = b
  pr2
    ( pr2
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = refl

  map-inv-compute-fib-map-prod :
    (t : C × D) → (fib f (pr1 t)) × (fib g (pr2 t)) → fib (map-prod f g) t
  pr1
    ( pr1
      ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
        ( pair (pair x refl) (pair y refl)))) = x
  pr2
    ( pr1
      ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
        ( pair (pair x refl) (pair y refl)))) = y
  pr2
    ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
      ( pair (pair x refl) (pair y refl))) = refl
  
  abstract
    issec-map-inv-compute-fib-map-prod :
      (t : C × D) →
      ((map-compute-fib-map-prod t) ∘ (map-inv-compute-fib-map-prod t)) ~ id
    issec-map-inv-compute-fib-map-prod (pair .(f x) .(g y))
      (pair (pair x refl) (pair y refl)) = refl

  abstract
    isretr-map-inv-compute-fib-map-prod :
      (t : C × D) →
      ((map-inv-compute-fib-map-prod t) ∘ (map-compute-fib-map-prod t)) ~ id
    isretr-map-inv-compute-fib-map-prod .(map-prod f g (pair a b))
      (pair (pair a b) refl) = refl

  abstract
    is-equiv-map-compute-fib-map-prod :
      (t : C × D) → is-equiv (map-compute-fib-map-prod t)
    is-equiv-map-compute-fib-map-prod t =
      is-equiv-has-inverse
        ( map-inv-compute-fib-map-prod t)
        ( issec-map-inv-compute-fib-map-prod t)
        ( isretr-map-inv-compute-fib-map-prod t)

  compute-fib-map-prod :
    (t : C × D) → fib (map-prod f g) t ≃ ((fib f (pr1 t)) × (fib g (pr2 t)))
  pr1 (compute-fib-map-prod t) = map-compute-fib-map-prod t
  pr2 (compute-fib-map-prod t) = is-equiv-map-compute-fib-map-prod t
```
