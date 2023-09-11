# Fibers of maps

```agda
module foundation-core.fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given a map `f : A → B` and a point `b : B`, the fiber of `f` at `b` is the
preimage of `f` at `b`. In other words, it consists of the elements `a : A`
equipped with an identification `Id (f a) b`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber : UU (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

  fiber' : UU (l1 ⊔ l2)
  fiber' = Σ A (λ x → b ＝ f x)
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fiber`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber : fiber f b → fiber f b → UU (l1 ⊔ l2)
  Eq-fiber s t = Σ (pr1 s ＝ pr1 t) (λ α → ((ap f α) ∙ (pr2 t)) ＝ (pr2 s))

  refl-Eq-fiber : (s : fiber f b) → Eq-fiber s s
  pr1 (refl-Eq-fiber s) = refl
  pr2 (refl-Eq-fiber s) = refl

  Eq-eq-fiber : {s t : fiber f b} → s ＝ t → Eq-fiber s t
  Eq-eq-fiber {s} refl = refl-Eq-fiber s

  eq-Eq-fiber-uncurry : {s t : fiber f b} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (refl , refl) = refl

  eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) →
    ((ap f α) ∙ (pr2 t)) ＝ pr2 s → s ＝ t
  eq-Eq-fiber α β = eq-Eq-fiber-uncurry (α , β)

  is-section-eq-Eq-fiber :
    {s t : fiber f b} → (Eq-eq-fiber {s} {t} ∘ eq-Eq-fiber-uncurry {s} {t}) ~ id
  is-section-eq-Eq-fiber (refl , refl) = refl

  is-retraction-eq-Eq-fiber :
    {s t : fiber f b} → (eq-Eq-fiber-uncurry {s} {t} ∘ Eq-eq-fiber {s} {t}) ~ id
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
```

#### The case of `fiber'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber' : fiber' f b → fiber' f b → UU (l1 ⊔ l2)
  Eq-fiber' s t = Σ (pr1 s ＝ pr1 t) (λ α → (pr2 t ＝ ((pr2 s) ∙ (ap f α))))

  refl-Eq-fiber' : (s : fiber' f b) → Eq-fiber' s s
  pr1 (refl-Eq-fiber' s) = refl
  pr2 (refl-Eq-fiber' s) = inv right-unit

  Eq-eq-fiber' : {s t : fiber' f b} → s ＝ t → Eq-fiber' s t
  Eq-eq-fiber' {s} refl = refl-Eq-fiber' s

  eq-Eq-fiber-uncurry' : {s t : fiber' f b} → Eq-fiber' s t → s ＝ t
  eq-Eq-fiber-uncurry' {x , p} (refl , refl) =
    ap (pair x) (inv right-unit)

  eq-Eq-fiber' :
    {s t : fiber' f b} (α : pr1 s ＝ pr1 t) →
    (pr2 t) ＝ ((pr2 s) ∙ (ap f α)) → s ＝ t
  eq-Eq-fiber' α β = eq-Eq-fiber-uncurry' (α , β)

  is-section-eq-Eq-fiber' :
    {s t : fiber' f b} →
    (Eq-eq-fiber' {s} {t} ∘ eq-Eq-fiber-uncurry' {s} {t}) ~ id
  is-section-eq-Eq-fiber' {x , refl} (refl , refl) = refl

  is-retraction-eq-Eq-fiber' :
    {s t : fiber' f b} →
    (eq-Eq-fiber-uncurry' {s} {t} ∘ Eq-eq-fiber' {s} {t}) ~ id
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
  pr1 (map-equiv-fiber (x , refl)) = x
  pr2 (map-equiv-fiber (x , refl)) = refl

  map-inv-equiv-fiber : fiber' f y → fiber f y
  pr1 (map-inv-equiv-fiber (x , refl)) = x
  pr2 (map-inv-equiv-fiber (x , refl)) = refl

  is-section-map-inv-equiv-fiber : (map-equiv-fiber ∘ map-inv-equiv-fiber) ~ id
  is-section-map-inv-equiv-fiber (x , refl) = refl

  is-retraction-map-inv-equiv-fiber :
    (map-inv-equiv-fiber ∘ map-equiv-fiber) ~ id
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
  pr1 (pr1 (map-inv-fiber-pr1 b)) = a
  pr2 (pr1 (map-inv-fiber-pr1 b)) = b
  pr2 (map-inv-fiber-pr1 b) = refl

  is-section-map-inv-fiber-pr1 : (map-inv-fiber-pr1 ∘ map-fiber-pr1) ~ id
  is-section-map-inv-fiber-pr1 ((.a , y) , refl) = refl

  is-retraction-map-inv-fiber-pr1 : (map-fiber-pr1 ∘ map-inv-fiber-pr1) ~ id
  is-retraction-map-inv-fiber-pr1 b = refl

  abstract
    is-equiv-map-fiber-pr1 : is-equiv map-fiber-pr1
    is-equiv-map-fiber-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-pr1
        is-retraction-map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1

  equiv-fiber-pr1 : fiber (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-pr1 = map-fiber-pr1
  pr2 equiv-fiber-pr1 = is-equiv-map-fiber-pr1

  abstract
    is-equiv-map-inv-fiber-pr1 : is-equiv map-inv-fiber-pr1
    is-equiv-map-inv-fiber-pr1 =
      is-equiv-is-invertible
        map-fiber-pr1
        is-section-map-inv-fiber-pr1
        is-retraction-map-inv-fiber-pr1

  inv-equiv-fiber-pr1 : B a ≃ fiber (pr1 {B = B}) a
  pr1 inv-equiv-fiber-pr1 = map-inv-fiber-pr1
  pr2 inv-equiv-fiber-pr1 = is-equiv-map-inv-fiber-pr1
```

### The total space of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber : (Σ B (fiber f)) → A
  map-equiv-total-fiber t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber : pr1 ~ (f ∘ map-equiv-total-fiber)
  triangle-map-equiv-total-fiber t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  pr1 (map-inv-equiv-total-fiber x) = f x
  pr1 (pr2 (map-inv-equiv-total-fiber x)) = x
  pr2 (pr2 (map-inv-equiv-total-fiber x)) = refl

  is-retraction-map-inv-equiv-total-fiber :
    (map-inv-equiv-total-fiber ∘ map-equiv-total-fiber) ~ id
  is-retraction-map-inv-equiv-total-fiber (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber :
    (map-equiv-total-fiber ∘ map-inv-equiv-total-fiber) ~ id
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

  inv-map-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) → fiber (g ∘ h) x
  pr1 (inv-map-compute-fiber-comp t) = pr1 (pr2 t)
  pr2 (inv-map-compute-fiber-comp t) =
    ap g (pr2 (pr2 t)) ∙ pr2 (pr1 t)

  is-section-inv-map-compute-fiber-comp :
    (map-compute-fiber-comp ∘ inv-map-compute-fiber-comp) ~ id
  is-section-inv-map-compute-fiber-comp
    ((.(h a) , refl) , (a , refl)) = refl

  is-retraction-inv-map-compute-fiber-comp :
    (inv-map-compute-fiber-comp ∘ map-compute-fiber-comp) ~ id
  is-retraction-inv-map-compute-fiber-comp (a , refl) = refl

  abstract
    is-equiv-map-compute-fiber-comp :
      is-equiv map-compute-fiber-comp
    is-equiv-map-compute-fiber-comp =
      is-equiv-is-invertible
        ( inv-map-compute-fiber-comp)
        ( is-section-inv-map-compute-fiber-comp)
        ( is-retraction-inv-map-compute-fiber-comp)

  equiv-compute-fiber-comp :
    fiber (g ∘ h) x ≃ Σ (fiber g x) (λ t → fiber h (pr1 t))
  pr1 equiv-compute-fiber-comp = map-compute-fiber-comp
  pr2 equiv-compute-fiber-comp = is-equiv-map-compute-fiber-comp

  abstract
    is-equiv-inv-map-compute-fiber-comp :
      is-equiv inv-map-compute-fiber-comp
    is-equiv-inv-map-compute-fiber-comp =
        is-equiv-is-invertible
          ( map-compute-fiber-comp)
          ( is-retraction-inv-map-compute-fiber-comp)
          ( is-section-inv-map-compute-fiber-comp)

  inv-equiv-compute-fiber-comp :
    Σ (fiber g x) (λ t → fiber h (pr1 t)) ≃ fiber (g ∘ h) x
  pr1 inv-equiv-compute-fiber-comp = inv-map-compute-fiber-comp
  pr2 inv-equiv-compute-fiber-comp = is-equiv-inv-map-compute-fiber-comp
```

### When a product is taken over all fibers of a map, then we can equivalently take the product over the domain of that map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fiber f y) → UU l3)
  where

  map-reduce-Π-fiber :
    ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
  map-reduce-Π-fiber h x = h (f x) (x , refl)

  inv-map-reduce-Π-fiber :
    ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
  inv-map-reduce-Π-fiber h .(f x) (x , refl) = h x

  is-section-inv-map-reduce-Π-fiber :
    (map-reduce-Π-fiber ∘ inv-map-reduce-Π-fiber) ~ id
  is-section-inv-map-reduce-Π-fiber h = refl

  is-retraction-inv-map-reduce-Π-fiber' :
    (h : (y : B) (z : fiber f y) → C y z) (y : B) →
    (inv-map-reduce-Π-fiber (map-reduce-Π-fiber h) y) ~ (h y)
  is-retraction-inv-map-reduce-Π-fiber' h .(f z) (z , refl) = refl

  is-retraction-inv-map-reduce-Π-fiber :
    (inv-map-reduce-Π-fiber ∘ map-reduce-Π-fiber) ~ id
  is-retraction-inv-map-reduce-Π-fiber h =
    eq-htpy (eq-htpy ∘ is-retraction-inv-map-reduce-Π-fiber' h)

  is-equiv-map-reduce-Π-fiber : is-equiv map-reduce-Π-fiber
  is-equiv-map-reduce-Π-fiber =
    is-equiv-is-invertible
      ( inv-map-reduce-Π-fiber)
      ( is-section-inv-map-reduce-Π-fiber)
      ( is-retraction-inv-map-reduce-Π-fiber)

  reduce-Π-fiber' :
    ((y : B) (z : fiber f y) → C y z) ≃ ((x : A) → C (f x) (x , refl))
  pr1 reduce-Π-fiber' = map-reduce-Π-fiber
  pr2 reduce-Π-fiber' = is-equiv-map-reduce-Π-fiber

reduce-Π-fiber :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fiber f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fiber f C = reduce-Π-fiber' f (λ y z → C y)
```
