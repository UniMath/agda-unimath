---
title: Fibers of maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.fibers-of-maps where

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation.function-extensionality
```

## Idea

Given a map `f : A → B` and a point `b : B`, the fiber of `f` at `b` is the preimage of `f` at `b`. In other words, it consists of the elements `a : A` equipped with an identification `Id (f a) b`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where
  
  fib : UU (l1 ⊔ l2)
  fib = Σ A (λ x → f x ＝ b)

  fib' : UU (l1 ⊔ l2)
  fib' = Σ A (λ x → b ＝ f x)
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fib`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fib : fib f b → fib f b → UU (l1 ⊔ l2)
  Eq-fib s t = Σ (pr1 s ＝ pr1 t) (λ α → ((ap f α) ∙ (pr2 t)) ＝ (pr2 s))

  refl-Eq-fib : (s : fib f b) → Eq-fib s s
  pr1 (refl-Eq-fib s) = refl
  pr2 (refl-Eq-fib s) = refl

  Eq-eq-fib : {s t : fib f b} → s ＝ t → Eq-fib s t
  Eq-eq-fib {s} refl = refl-Eq-fib s

  eq-Eq-fib-uncurry : {s t : fib f b} → Eq-fib s t → s ＝ t
  eq-Eq-fib-uncurry {pair x p} {pair .x .p} (pair refl refl) = refl

  eq-Eq-fib :
    {s t : fib f b} (α : pr1 s ＝ pr1 t) →
    ((ap f α) ∙ (pr2 t)) ＝ pr2 s → s ＝ t
  eq-Eq-fib α β = eq-Eq-fib-uncurry (pair α β)

  issec-eq-Eq-fib :
    {s t : fib f b} → (Eq-eq-fib {s} {t} ∘ eq-Eq-fib-uncurry {s} {t}) ~ id
  issec-eq-Eq-fib {pair x p} {pair .x .p} (pair refl refl) = refl

  isretr-eq-Eq-fib :
    {s t : fib f b} → (eq-Eq-fib-uncurry {s} {t} ∘ Eq-eq-fib {s} {t}) ~ id
  isretr-eq-Eq-fib {pair x p} {.(pair x p)} refl = refl

  abstract
    is-equiv-Eq-eq-fib : {s t : fib f b} → is-equiv (Eq-eq-fib {s} {t})
    is-equiv-Eq-eq-fib {s} {t} =
      is-equiv-has-inverse
        eq-Eq-fib-uncurry
        issec-eq-Eq-fib
        isretr-eq-Eq-fib

  equiv-Eq-eq-fib : {s t : fib f b} → (s ＝ t) ≃ Eq-fib s t
  pr1 (equiv-Eq-eq-fib {s} {t}) = Eq-eq-fib
  pr2 (equiv-Eq-eq-fib {s} {t}) = is-equiv-Eq-eq-fib

  abstract
    is-equiv-eq-Eq-fib :
      {s t : fib f b} → is-equiv (eq-Eq-fib-uncurry {s} {t})
    is-equiv-eq-Eq-fib {s} {t} =
      is-equiv-has-inverse
        Eq-eq-fib
        isretr-eq-Eq-fib
        issec-eq-Eq-fib

  equiv-eq-Eq-fib : {s t : fib f b} → Eq-fib s t ≃ (s ＝ t)
  pr1 (equiv-eq-Eq-fib {s} {t}) = eq-Eq-fib-uncurry
  pr2 (equiv-eq-Eq-fib {s} {t}) = is-equiv-eq-Eq-fib
```

#### The case of `fib'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fib' : fib' f b → fib' f b → UU (l1 ⊔ l2)
  Eq-fib' s t = Σ (pr1 s ＝ pr1 t) (λ α → (pr2 t ＝ ((pr2 s) ∙ (ap f α))))

  refl-Eq-fib' : (s : fib' f b) → Eq-fib' s s
  pr1 (refl-Eq-fib' s) = refl
  pr2 (refl-Eq-fib' s) = inv right-unit

  Eq-eq-fib' : {s t : fib' f b} → s ＝ t → Eq-fib' s t
  Eq-eq-fib' {s} refl = refl-Eq-fib' s

  eq-Eq-fib-uncurry' : {s t : fib' f b} → Eq-fib' s t → s ＝ t
  eq-Eq-fib-uncurry' {pair x p} {pair .x .(p ∙ refl)} (pair refl refl) =
    ap (pair x) (inv right-unit)

  eq-Eq-fib' :
    {s t : fib' f b} (α : pr1 s ＝ pr1 t) →
    (pr2 t) ＝ ((pr2 s) ∙ (ap f α)) → s ＝ t
  eq-Eq-fib' α β = eq-Eq-fib-uncurry' (pair α β)

  issec-eq-Eq-fib' :
    {s t : fib' f b} → (Eq-eq-fib' {s} {t} ∘ eq-Eq-fib-uncurry' {s} {t}) ~ id
  issec-eq-Eq-fib' {pair x refl} {pair .x .refl} (pair refl refl) = refl

  isretr-eq-Eq-fib' :
    {s t : fib' f b} → (eq-Eq-fib-uncurry' {s} {t} ∘ Eq-eq-fib' {s} {t}) ~ id
  isretr-eq-Eq-fib' {pair x refl} {.(pair x refl)} refl = refl

  abstract
    is-equiv-Eq-eq-fib' : {s t : fib' f b} → is-equiv (Eq-eq-fib' {s} {t})
    is-equiv-Eq-eq-fib' {s} {t} =
      is-equiv-has-inverse
        eq-Eq-fib-uncurry'
        issec-eq-Eq-fib'
        isretr-eq-Eq-fib'

  equiv-Eq-eq-fib' : {s t : fib' f b} → (s ＝ t) ≃ Eq-fib' s t
  pr1 (equiv-Eq-eq-fib' {s} {t}) = Eq-eq-fib'
  pr2 (equiv-Eq-eq-fib' {s} {t}) = is-equiv-Eq-eq-fib'

  abstract
    is-equiv-eq-Eq-fib' :
      {s t : fib' f b} → is-equiv (eq-Eq-fib-uncurry' {s} {t})
    is-equiv-eq-Eq-fib' {s} {t} =
      is-equiv-has-inverse
        Eq-eq-fib'
        isretr-eq-Eq-fib'
        issec-eq-Eq-fib'

  equiv-eq-Eq-fib' : {s t : fib' f b} → Eq-fib' s t ≃ (s ＝ t)
  pr1 (equiv-eq-Eq-fib' {s} {t}) = eq-Eq-fib-uncurry'
  pr2 (equiv-eq-Eq-fib' {s} {t}) = is-equiv-eq-Eq-fib'
```

### `fib f y` and `fib' f y` are equivalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where
  
  map-equiv-fib : fib f y → fib' f y
  map-equiv-fib (pair x refl) = pair x refl

  map-inv-equiv-fib : fib' f y → fib f y
  map-inv-equiv-fib (pair x refl) = pair x refl

  issec-map-inv-equiv-fib : (map-equiv-fib ∘ map-inv-equiv-fib) ~ id
  issec-map-inv-equiv-fib (pair x refl) = refl

  isretr-map-inv-equiv-fib : (map-inv-equiv-fib ∘ map-equiv-fib) ~ id
  isretr-map-inv-equiv-fib (pair x refl) = refl

  is-equiv-map-equiv-fib : is-equiv map-equiv-fib
  is-equiv-map-equiv-fib =
    is-equiv-has-inverse
      map-inv-equiv-fib
      issec-map-inv-equiv-fib
      isretr-map-inv-equiv-fib

  equiv-fib : fib f y ≃ fib' f y
  pr1 equiv-fib = map-equiv-fib
  pr2 equiv-fib = is-equiv-map-equiv-fib
```

### Computing the fibers of a projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fib-pr1 : fib (pr1 {B = B}) a → B a
  map-fib-pr1 (pair (pair x y) p) = tr B p y

  map-inv-fib-pr1 : B a → fib (pr1 {B = B}) a
  map-inv-fib-pr1 b = pair (pair a b) refl

  issec-map-inv-fib-pr1 : (map-inv-fib-pr1 ∘ map-fib-pr1) ~ id
  issec-map-inv-fib-pr1 (pair (pair .a y) refl) = refl

  isretr-map-inv-fib-pr1 : (map-fib-pr1 ∘ map-inv-fib-pr1) ~ id
  isretr-map-inv-fib-pr1 b = refl

  abstract
    is-equiv-map-fib-pr1 : is-equiv map-fib-pr1
    is-equiv-map-fib-pr1 =
      is-equiv-has-inverse
        map-inv-fib-pr1
        isretr-map-inv-fib-pr1
        issec-map-inv-fib-pr1

  equiv-fib-pr1 : fib (pr1 {B = B}) a ≃ B a
  pr1 equiv-fib-pr1 = map-fib-pr1
  pr2 equiv-fib-pr1 = is-equiv-map-fib-pr1

  abstract
    is-equiv-map-inv-fib-pr1 : is-equiv map-inv-fib-pr1
    is-equiv-map-inv-fib-pr1 =
      is-equiv-has-inverse
        map-fib-pr1
        issec-map-inv-fib-pr1
        isretr-map-inv-fib-pr1

  inv-equiv-fib-pr1 : B a ≃ fib (pr1 {B = B}) a
  pr1 inv-equiv-fib-pr1 = map-inv-fib-pr1
  pr2 inv-equiv-fib-pr1 = is-equiv-map-inv-fib-pr1
```

### The total space of fibers

```
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  map-equiv-total-fib : (Σ B (fib f)) → A
  map-equiv-total-fib t = pr1 (pr2 t)

  triangle-map-equiv-total-fib : pr1 ~ (f ∘ map-equiv-total-fib)
  triangle-map-equiv-total-fib t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fib : A → Σ B (fib f)
  map-inv-equiv-total-fib x = pair (f x) (pair x refl)

  isretr-map-inv-equiv-total-fib :
    (map-inv-equiv-total-fib ∘ map-equiv-total-fib) ~ id
  isretr-map-inv-equiv-total-fib (pair .(f x) (pair x refl)) = refl

  issec-map-inv-equiv-total-fib :
    (map-equiv-total-fib ∘ map-inv-equiv-total-fib) ~ id
  issec-map-inv-equiv-total-fib x = refl

  abstract
    is-equiv-map-equiv-total-fib : is-equiv map-equiv-total-fib
    is-equiv-map-equiv-total-fib =
      is-equiv-has-inverse
        map-inv-equiv-total-fib
        issec-map-inv-equiv-total-fib
        isretr-map-inv-equiv-total-fib

    is-equiv-map-inv-equiv-total-fib : is-equiv map-inv-equiv-total-fib
    is-equiv-map-inv-equiv-total-fib =
      is-equiv-has-inverse
        map-equiv-total-fib
        isretr-map-inv-equiv-total-fib
        issec-map-inv-equiv-total-fib

  equiv-total-fib : Σ B (fib f) ≃ A
  pr1 equiv-total-fib = map-equiv-total-fib
  pr2 equiv-total-fib = is-equiv-map-equiv-total-fib

  inv-equiv-total-fib : A ≃ Σ B (fib f)
  pr1 inv-equiv-total-fib = map-inv-equiv-total-fib
  pr2 inv-equiv-total-fib = is-equiv-map-inv-equiv-total-fib
```

### Fibers of compositions

```agda
map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
pr1 (pr1 (map-compute-fib-comp g h x (pair a p))) = h a
pr2 (pr1 (map-compute-fib-comp g h x (pair a p))) = p
pr1 (pr2 (map-compute-fib-comp g h x (pair a p))) = a
pr2 (pr2 (map-compute-fib-comp g h x (pair a p))) = refl

inv-map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
pr1 (inv-map-compute-fib-comp g h c t) = pr1 (pr2 t)
pr2 (inv-map-compute-fib-comp g h c t) = (ap g (pr2 (pr2 t))) ∙ (pr2 (pr1 t))

issec-inv-map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) →
  ((map-compute-fib-comp g h x) ∘ (inv-map-compute-fib-comp g h x)) ~ id
issec-inv-map-compute-fib-comp g h x
  (pair (pair .(h a) refl) (pair a refl)) = refl

isretr-inv-map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) (x : X) →
  ((inv-map-compute-fib-comp g h x) ∘ (map-compute-fib-comp g h x)) ~ id
isretr-inv-map-compute-fib-comp g h .(g (h a)) (pair a refl) = refl

abstract
  is-equiv-map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (map-compute-fib-comp g h x)
  is-equiv-map-compute-fib-comp g h x =
    is-equiv-has-inverse
      ( inv-map-compute-fib-comp g h x)
      ( issec-inv-map-compute-fib-comp g h x)
      ( isretr-inv-map-compute-fib-comp g h x)

abstract
  is-equiv-inv-map-compute-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (inv-map-compute-fib-comp g h x)
  is-equiv-inv-map-compute-fib-comp g h x =
    is-equiv-has-inverse
      ( map-compute-fib-comp g h x)
      ( isretr-inv-map-compute-fib-comp g h x)
      ( issec-inv-map-compute-fib-comp g h x)
```

### When a product is taken over all fibers of a map, then we can equivalently take the product over the domain of that map.

```agda
map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) → ((x : A) → C (f x) (pair x refl))
map-reduce-Π-fib f C h x = h (f x) (pair x refl)

inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((x : A) → C (f x) (pair x refl)) → ((y : B) (z : fib f y) → C y z)
inv-map-reduce-Π-fib f C h .(f x) (pair x refl) = h x

issec-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((map-reduce-Π-fib f C) ∘ (inv-map-reduce-Π-fib f C)) ~ id
issec-inv-map-reduce-Π-fib f C h = refl

isretr-inv-map-reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  (h : (y : B) (z : fib f y) → C y z) (y : B) →
  (inv-map-reduce-Π-fib f C ((map-reduce-Π-fib f C) h) y) ~ (h y)
isretr-inv-map-reduce-Π-fib' f C h .(f z) (pair z refl) = refl

isretr-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((inv-map-reduce-Π-fib f C) ∘ (map-reduce-Π-fib f C)) ~ id
isretr-inv-map-reduce-Π-fib f C h =
  eq-htpy (λ y → eq-htpy (isretr-inv-map-reduce-Π-fib' f C h y))

is-equiv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  is-equiv (map-reduce-Π-fib f C)
is-equiv-map-reduce-Π-fib f C =
  is-equiv-has-inverse
    ( inv-map-reduce-Π-fib f C)
    ( issec-inv-map-reduce-Π-fib f C)
    ( isretr-inv-map-reduce-Π-fib f C)

reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) ≃ ((x : A) → C (f x) (pair x refl))
pr1 (reduce-Π-fib' f C) = map-reduce-Π-fib f C
pr2 (reduce-Π-fib' f C) = is-equiv-map-reduce-Π-fib f C

reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fib f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fib f C = reduce-Π-fib' f (λ y z → C y)
```
