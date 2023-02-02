---
title: Maps fibered over a map
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.fibered-maps where

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.slice
open import foundation.universe-levels
```

## Idea

Consider a diagram of the form

```md
  A        B
  |        |
 f|        |g
  |        |
  V        V
  X -----> Y
       i
```

A fibered map from `f` to `g` over `i` is a map `h : A → B` such that the square `(i ∘ f) ~ (g ∘ h)` commutes.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  hom-over-morphism :
    (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ l2 ⊔ l4)
  hom-over-morphism i f g = hom-slice (i ∘ f) g

  fiberwise-hom-hom-over-morphism :
    (i : X → Y) (f : A → X) (g : B → Y) →
    hom-over-morphism i f g → (x : X) → (fib f x) → (fib g (i x))
  pr1 (fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl)) =
    h a
  pr2 (fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl)) =
    inv (H a)

  hom-over-morphism-fiberwise-hom :
    (i : X → Y) (f : A → X) (g : B → Y) →
    ((x : X) → (fib f x) → (fib g (i x))) → hom-over-morphism i f g
  pr1 (hom-over-morphism-fiberwise-hom i f g α) a = pr1 (α (f a) (pair a refl))
  pr2 (hom-over-morphism-fiberwise-hom i f g α) a =
    inv (pr2 (α (f a) (pair a refl)))

  issec-hom-over-morphism-fiberwise-hom-eq-htpy :
    (i : X → Y) (f : A → X) (g : B → Y) →
    (α : (x : X) → (fib f x) → (fib g (i x))) (x : X) →
    ( fiberwise-hom-hom-over-morphism i f g
      ( hom-over-morphism-fiberwise-hom i f g α) x) ~ (α x)
  issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α .(f a) (pair a refl) =
    eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

  issec-hom-over-morphism-fiberwise-hom :
    (i : X → Y) (f : A → X) (g : B → Y) →
    ( ( fiberwise-hom-hom-over-morphism i f g) ∘
      ( hom-over-morphism-fiberwise-hom i f g)) ~ id
  issec-hom-over-morphism-fiberwise-hom i f g α =
    eq-htpy
      ( λ x →
        ( eq-htpy
          ( issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α x)))

  isretr-hom-over-morphism-fiberwise-hom :
    (i : X → Y) (f : A → X) (g : B → Y) →
    ( ( hom-over-morphism-fiberwise-hom i f g) ∘
      ( fiberwise-hom-hom-over-morphism i f g)) ~ id
  isretr-hom-over-morphism-fiberwise-hom i f g (pair h H) =
    eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

  abstract
    is-equiv-fiberwise-hom-hom-over-morphism :
      (i : X → Y) (f : A → X) (g : B → Y) →
      is-equiv (fiberwise-hom-hom-over-morphism i f g)
    is-equiv-fiberwise-hom-hom-over-morphism i f g =
      is-equiv-has-inverse
        ( hom-over-morphism-fiberwise-hom i f g)
        ( issec-hom-over-morphism-fiberwise-hom i f g)
        ( isretr-hom-over-morphism-fiberwise-hom i f g)

  abstract
    is-equiv-hom-over-morphism-fiberwise-hom :
      (i : X → Y) (f : A → X) (g : B → Y) →
      is-equiv (hom-over-morphism-fiberwise-hom i f g)
    is-equiv-hom-over-morphism-fiberwise-hom i f g =
      is-equiv-has-inverse
        ( fiberwise-hom-hom-over-morphism i f g)
        ( isretr-hom-over-morphism-fiberwise-hom i f g)
        ( issec-hom-over-morphism-fiberwise-hom i f g)
```
