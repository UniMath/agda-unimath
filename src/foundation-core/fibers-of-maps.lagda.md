# Fibers of maps

```agda
module foundation-core.fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given a map `f : A → B` and an element `b : B`, the **fiber** of `f` at `b` is
the preimage of `f` at `b`. In other words, it consists of the elements `a : A`
equipped with an [identification](foundation-core.identity-types.md) `f a ＝ b`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber : UU (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

  fiber' : UU (l1 ⊔ l2)
  fiber' = Σ A (λ x → b ＝ f x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  inclusion-fiber : fiber f b → A
  inclusion-fiber = pr1

  compute-value-inclusion-fiber : (y : fiber f b) → f (inclusion-fiber y) ＝ b
  compute-value-inclusion-fiber = pr2

  inclusion-fiber' : fiber' f b → A
  inclusion-fiber' = pr1

  compute-value-inclusion-fiber' :
    (y : fiber' f b) → b ＝ f (inclusion-fiber' y)
  compute-value-inclusion-fiber' = pr2
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fiber`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber : fiber f b → fiber f b → UU (l1 ⊔ l2)
  Eq-fiber s t = Σ (pr1 s ＝ pr1 t) (λ α → ap f α ∙ pr2 t ＝ pr2 s)

  refl-Eq-fiber : (s : fiber f b) → Eq-fiber s s
  pr1 (refl-Eq-fiber s) = refl
  pr2 (refl-Eq-fiber s) = refl

  Eq-eq-fiber : {s t : fiber f b} → s ＝ t → Eq-fiber s t
  Eq-eq-fiber {s} refl = refl-Eq-fiber s

  eq-Eq-fiber-uncurry : {s t : fiber f b} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (refl , refl) = refl

  eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) → ap f α ∙ pr2 t ＝ pr2 s → s ＝ t
  eq-Eq-fiber α β = eq-Eq-fiber-uncurry (α , β)

  is-section-eq-Eq-fiber :
    {s t : fiber f b} →
    is-section (Eq-eq-fiber {s} {t}) (eq-Eq-fiber-uncurry {s} {t})
  is-section-eq-Eq-fiber (refl , refl) = refl

  is-retraction-eq-Eq-fiber :
    {s t : fiber f b} →
    is-retraction (Eq-eq-fiber {s} {t}) (eq-Eq-fiber-uncurry {s} {t})
  is-retraction-eq-Eq-fiber refl = refl

  abstract
    is-equiv-Eq-eq-fiber : {s t : fiber f b} → is-equiv (Eq-eq-fiber {s} {t})
    is-equiv-Eq-eq-fiber =
      is-equiv-is-invertible
        eq-Eq-fiber-uncurry
        is-section-eq-Eq-fiber
        is-retraction-eq-Eq-fiber

  equiv-Eq-eq-fiber : {s t : fiber f b} → (s ＝ t) ≃ Eq-fiber s t
  pr1 equiv-Eq-eq-fiber = Eq-eq-fiber
  pr2 equiv-Eq-eq-fiber = is-equiv-Eq-eq-fiber

  abstract
    is-equiv-eq-Eq-fiber :
      {s t : fiber f b} → is-equiv (eq-Eq-fiber-uncurry {s} {t})
    is-equiv-eq-Eq-fiber =
      is-equiv-is-invertible
        Eq-eq-fiber
        is-retraction-eq-Eq-fiber
        is-section-eq-Eq-fiber

  equiv-eq-Eq-fiber : {s t : fiber f b} → Eq-fiber s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber = eq-Eq-fiber-uncurry
  pr2 equiv-eq-Eq-fiber = is-equiv-eq-Eq-fiber

  compute-ap-inclusion-fiber-eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) (β : ap f α ∙ pr2 t ＝ pr2 s) →
    ap (inclusion-fiber f) (eq-Eq-fiber α β) ＝ α
  compute-ap-inclusion-fiber-eq-Eq-fiber refl refl = refl
```

#### The case of `fiber'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber' : fiber' f b → fiber' f b → UU (l1 ⊔ l2)
  Eq-fiber' s t = Σ (pr1 s ＝ pr1 t) (λ α → pr2 t ＝ pr2 s ∙ ap f α)

  refl-Eq-fiber' : (s : fiber' f b) → Eq-fiber' s s
  pr1 (refl-Eq-fiber' s) = refl
  pr2 (refl-Eq-fiber' s) = inv right-unit

  Eq-eq-fiber' : {s t : fiber' f b} → s ＝ t → Eq-fiber' s t
  Eq-eq-fiber' {s} refl = refl-Eq-fiber' s

  eq-Eq-fiber-uncurry' : {s t : fiber' f b} → Eq-fiber' s t → s ＝ t
  eq-Eq-fiber-uncurry' {x , p} (refl , refl) =
    ap (pair _) (inv right-unit)

  eq-Eq-fiber' :
    {s t : fiber' f b} (α : pr1 s ＝ pr1 t) → pr2 t ＝ pr2 s ∙ ap f α → s ＝ t
  eq-Eq-fiber' α β = eq-Eq-fiber-uncurry' (α , β)

  is-section-eq-Eq-fiber' :
    {s t : fiber' f b} →
    is-section (Eq-eq-fiber' {s} {t}) (eq-Eq-fiber-uncurry' {s} {t})
  is-section-eq-Eq-fiber' {x , refl} (refl , refl) = refl

  is-retraction-eq-Eq-fiber' :
    {s t : fiber' f b} →
    is-retraction (Eq-eq-fiber' {s} {t}) (eq-Eq-fiber-uncurry' {s} {t})
  is-retraction-eq-Eq-fiber' {x , refl} refl = refl

  abstract
    is-equiv-Eq-eq-fiber' :
      {s t : fiber' f b} → is-equiv (Eq-eq-fiber' {s} {t})
    is-equiv-Eq-eq-fiber' =
      is-equiv-is-invertible
        eq-Eq-fiber-uncurry'
        is-section-eq-Eq-fiber'
        is-retraction-eq-Eq-fiber'

  equiv-Eq-eq-fiber' : {s t : fiber' f b} → (s ＝ t) ≃ Eq-fiber' s t
  pr1 equiv-Eq-eq-fiber' = Eq-eq-fiber'
  pr2 equiv-Eq-eq-fiber' = is-equiv-Eq-eq-fiber'

  abstract
    is-equiv-eq-Eq-fiber' :
      {s t : fiber' f b} → is-equiv (eq-Eq-fiber-uncurry' {s} {t})
    is-equiv-eq-Eq-fiber' =
      is-equiv-is-invertible
        Eq-eq-fiber'
        is-retraction-eq-Eq-fiber'
        is-section-eq-Eq-fiber'

  equiv-eq-Eq-fiber' : {s t : fiber' f b} → Eq-fiber' s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber' = eq-Eq-fiber-uncurry'
  pr2 equiv-eq-Eq-fiber' = is-equiv-eq-Eq-fiber'
```

### `fiber f y` and `fiber' f y` are equivalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  map-equiv-fiber : fiber f y → fiber' f y
  pr1 (map-equiv-fiber (x , _)) = x
  pr2 (map-equiv-fiber (x , p)) = inv p

  map-inv-equiv-fiber : fiber' f y → fiber f y
  pr1 (map-inv-equiv-fiber (x , _)) = x
  pr2 (map-inv-equiv-fiber (x , p)) = inv p

  is-section-map-inv-equiv-fiber :
    is-section map-equiv-fiber map-inv-equiv-fiber
  is-section-map-inv-equiv-fiber (x , refl) = refl

  is-retraction-map-inv-equiv-fiber :
    is-retraction map-equiv-fiber map-inv-equiv-fiber
  is-retraction-map-inv-equiv-fiber (x , refl) = refl

  is-equiv-map-equiv-fiber : is-equiv map-equiv-fiber
  is-equiv-map-equiv-fiber =
    is-equiv-is-invertible
      map-inv-equiv-fiber
      is-section-map-inv-equiv-fiber
      is-retraction-map-inv-equiv-fiber

  equiv-fiber : fiber f y ≃ fiber' f y
  pr1 equiv-fiber = map-equiv-fiber
  pr2 equiv-fiber = is-equiv-map-equiv-fiber
```

### Computing the fibers of a projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fiber-pr1 : fiber (pr1 {B = B}) a → B a
  map-fiber-pr1 ((x , y) , p) = tr B p y

  map-inv-fiber-pr1 : B a → fiber (pr1 {B = B}) a
  map-inv-fiber-pr1 b = (a , b) , refl

  is-section-map-inv-fiber-pr1 :
    is-section map-fiber-pr1 map-inv-fiber-pr1
  is-section-map-inv-fiber-pr1 b = refl

  is-retraction-map-inv-fiber-pr1 :
    is-retraction map-fiber-pr1 map-inv-fiber-pr1
  is-retraction-map-inv-fiber-pr1 ((.a , y) , refl) = refl

  abstract
    is-equiv-map-fiber-pr1 : is-equiv map-fiber-pr1
    is-equiv-map-fiber-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1
        is-retraction-map-inv-fiber-pr1

  equiv-fiber-pr1 : fiber (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-pr1 = map-fiber-pr1
  pr2 equiv-fiber-pr1 = is-equiv-map-fiber-pr1

  abstract
    is-equiv-map-inv-fiber-pr1 : is-equiv map-inv-fiber-pr1
    is-equiv-map-inv-fiber-pr1 =
      is-equiv-is-invertible
        map-fiber-pr1
        is-retraction-map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1

  inv-equiv-fiber-pr1 : B a ≃ fiber (pr1 {B = B}) a
  pr1 inv-equiv-fiber-pr1 = map-inv-fiber-pr1
  pr2 inv-equiv-fiber-pr1 = is-equiv-map-inv-fiber-pr1
```

### The total space of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber : Σ B (fiber f) → A
  map-equiv-total-fiber t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber : pr1 ~ f ∘ map-equiv-total-fiber
  triangle-map-equiv-total-fiber t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  map-inv-equiv-total-fiber x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber :
    is-retraction map-equiv-total-fiber map-inv-equiv-total-fiber
  is-retraction-map-inv-equiv-total-fiber (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber :
    is-section map-equiv-total-fiber map-inv-equiv-total-fiber
  is-section-map-inv-equiv-total-fiber x = refl

  abstract
    is-equiv-map-equiv-total-fiber : is-equiv map-equiv-total-fiber
    is-equiv-map-equiv-total-fiber =
      is-equiv-is-invertible
        map-inv-equiv-total-fiber
        is-section-map-inv-equiv-total-fiber
        is-retraction-map-inv-equiv-total-fiber

    is-equiv-map-inv-equiv-total-fiber : is-equiv map-inv-equiv-total-fiber
    is-equiv-map-inv-equiv-total-fiber =
      is-equiv-is-invertible
        map-equiv-total-fiber
        is-retraction-map-inv-equiv-total-fiber
        is-section-map-inv-equiv-total-fiber

  equiv-total-fiber : Σ B (fiber f) ≃ A
  pr1 equiv-total-fiber = map-equiv-total-fiber
  pr2 equiv-total-fiber = is-equiv-map-equiv-total-fiber

  inv-equiv-total-fiber : A ≃ Σ B (fiber f)
  pr1 inv-equiv-total-fiber = map-inv-equiv-total-fiber
  pr2 inv-equiv-total-fiber = is-equiv-map-inv-equiv-total-fiber
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber' : Σ B (fiber' f) → A
  map-equiv-total-fiber' t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber' : pr1 ~ f ∘ map-equiv-total-fiber'
  triangle-map-equiv-total-fiber' t = pr2 (pr2 t)

  map-inv-equiv-total-fiber' : A → Σ B (fiber' f)
  map-inv-equiv-total-fiber' x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber' :
    is-retraction map-equiv-total-fiber' map-inv-equiv-total-fiber'
  is-retraction-map-inv-equiv-total-fiber' (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber' :
    is-section map-equiv-total-fiber' map-inv-equiv-total-fiber'
  is-section-map-inv-equiv-total-fiber' x = refl

  is-equiv-map-equiv-total-fiber' : is-equiv map-equiv-total-fiber'
  is-equiv-map-equiv-total-fiber' =
    is-equiv-is-invertible
      ( map-inv-equiv-total-fiber')
      ( is-section-map-inv-equiv-total-fiber')
      ( is-retraction-map-inv-equiv-total-fiber')

  is-equiv-map-inv-equiv-total-fiber' : is-equiv map-inv-equiv-total-fiber'
  is-equiv-map-inv-equiv-total-fiber' =
    is-equiv-is-invertible
      map-equiv-total-fiber'
      is-retraction-map-inv-equiv-total-fiber'
      is-section-map-inv-equiv-total-fiber'

  equiv-total-fiber' : Σ B (fiber' f) ≃ A
  pr1 equiv-total-fiber' = map-equiv-total-fiber'
  pr2 equiv-total-fiber' = is-equiv-map-equiv-total-fiber'

  inv-equiv-total-fiber' : A ≃ Σ B (fiber' f)
  pr1 inv-equiv-total-fiber' = map-inv-equiv-total-fiber'
  pr2 inv-equiv-total-fiber' = is-equiv-map-inv-equiv-total-fiber'
```

### Fibers of compositions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (x : X)
  where

  map-compute-fiber-comp :
    fiber (g ∘ h) x → Σ (fiber g x) (λ t → fiber h (pr1 t))
  pr1 (pr1 (map-compute-fiber-comp (a , p))) = h a
  pr2 (pr1 (map-compute-fiber-comp (a , p))) = p
  pr1 (pr2 (map-compute-fiber-comp (a , p))) = a
  pr2 (pr2 (map-compute-fiber-comp (a , p))) = refl

  map-inv-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) → fiber (g ∘ h) x
  pr1 (map-inv-compute-fiber-comp t) = pr1 (pr2 t)
  pr2 (map-inv-compute-fiber-comp t) = ap g (pr2 (pr2 t)) ∙ pr2 (pr1 t)

  inclusion-fiber-comp : (t : fiber g x) → fiber h (pr1 t) → fiber (g ∘ h) x
  inclusion-fiber-comp t s = map-inv-compute-fiber-comp (t , s)

  is-section-map-inv-compute-fiber-comp :
    is-section map-compute-fiber-comp map-inv-compute-fiber-comp
  is-section-map-inv-compute-fiber-comp ((.(h a) , refl) , (a , refl)) = refl

  is-retraction-map-inv-compute-fiber-comp :
    is-retraction map-compute-fiber-comp map-inv-compute-fiber-comp
  is-retraction-map-inv-compute-fiber-comp (a , refl) = refl

  abstract
    is-equiv-map-compute-fiber-comp :
      is-equiv map-compute-fiber-comp
    is-equiv-map-compute-fiber-comp =
      is-equiv-is-invertible
        ( map-inv-compute-fiber-comp)
        ( is-section-map-inv-compute-fiber-comp)
        ( is-retraction-map-inv-compute-fiber-comp)

  compute-fiber-comp :
    fiber (g ∘ h) x ≃ Σ (fiber g x) (λ t → fiber h (pr1 t))
  pr1 compute-fiber-comp = map-compute-fiber-comp
  pr2 compute-fiber-comp = is-equiv-map-compute-fiber-comp

  abstract
    is-equiv-map-inv-compute-fiber-comp :
      is-equiv map-inv-compute-fiber-comp
    is-equiv-map-inv-compute-fiber-comp =
        is-equiv-is-invertible
          ( map-compute-fiber-comp)
          ( is-retraction-map-inv-compute-fiber-comp)
          ( is-section-map-inv-compute-fiber-comp)

  inv-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) ≃ fiber (g ∘ h) x
  pr1 inv-compute-fiber-comp = map-inv-compute-fiber-comp
  pr2 inv-compute-fiber-comp = is-equiv-map-inv-compute-fiber-comp
```

### Fibers of homotopic maps are equivalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-htpy : fiber f y → fiber g y
  map-equiv-fiber-htpy (x , p) = x , H x ∙ᵣ p

  map-inv-equiv-fiber-htpy : fiber g y → fiber f y
  map-inv-equiv-fiber-htpy (x , p) = x , inv (H x) ∙ᵣ p

  is-section-map-inv-equiv-fiber-htpy :
    is-section map-equiv-fiber-htpy map-inv-equiv-fiber-htpy
  is-section-map-inv-equiv-fiber-htpy (x , refl) =
    eq-Eq-fiber g (g x) refl (inv (right-inv-right-strict-concat (H x)))

  is-retraction-map-inv-equiv-fiber-htpy :
    is-retraction map-equiv-fiber-htpy map-inv-equiv-fiber-htpy
  is-retraction-map-inv-equiv-fiber-htpy (x , refl) =
    eq-Eq-fiber f (f x) refl (inv (left-inv-right-strict-concat (H x)))

  is-equiv-map-equiv-fiber-htpy : is-equiv map-equiv-fiber-htpy
  is-equiv-map-equiv-fiber-htpy =
    is-equiv-is-invertible
      map-inv-equiv-fiber-htpy
      is-section-map-inv-equiv-fiber-htpy
      is-retraction-map-inv-equiv-fiber-htpy

  equiv-fiber-htpy : fiber f y ≃ fiber g y
  equiv-fiber-htpy = map-equiv-fiber-htpy , is-equiv-map-equiv-fiber-htpy
```

We repeat the construction for `fiber'`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-htpy' : fiber' f y → fiber' g y
  map-equiv-fiber-htpy' (x , p) = (x , p ∙ inv (H x))

  map-inv-equiv-fiber-htpy' : fiber' g y → fiber' f y
  map-inv-equiv-fiber-htpy' (x , p) = (x , p ∙ H x)

  is-section-map-inv-equiv-fiber-htpy' :
    is-section map-equiv-fiber-htpy' map-inv-equiv-fiber-htpy'
  is-section-map-inv-equiv-fiber-htpy' (x , p) =
    ap (pair x) (is-retraction-inv-concat' (H x) p)

  is-retraction-map-inv-equiv-fiber-htpy' :
    is-retraction map-equiv-fiber-htpy' map-inv-equiv-fiber-htpy'
  is-retraction-map-inv-equiv-fiber-htpy' (x , p) =
    ap (pair x) (is-section-inv-concat' (H x) p)

  is-equiv-map-equiv-fiber-htpy' : is-equiv map-equiv-fiber-htpy'
  is-equiv-map-equiv-fiber-htpy' =
    is-equiv-is-invertible
      map-inv-equiv-fiber-htpy'
      is-section-map-inv-equiv-fiber-htpy'
      is-retraction-map-inv-equiv-fiber-htpy'

  equiv-fiber-htpy' : fiber' f y ≃ fiber' g y
  equiv-fiber-htpy' = map-equiv-fiber-htpy' , is-equiv-map-equiv-fiber-htpy'
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
