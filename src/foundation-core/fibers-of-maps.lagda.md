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
open import foundation-core.transport
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
  eq-Eq-fib-uncurry (refl , refl) = refl

  eq-Eq-fib :
    {s t : fib f b} (α : pr1 s ＝ pr1 t) →
    ((ap f α) ∙ (pr2 t)) ＝ pr2 s → s ＝ t
  eq-Eq-fib α β = eq-Eq-fib-uncurry (α , β)

  is-section-eq-Eq-fib :
    {s t : fib f b} → (Eq-eq-fib {s} {t} ∘ eq-Eq-fib-uncurry {s} {t}) ~ id
  is-section-eq-Eq-fib (refl , refl) = refl

  is-retraction-eq-Eq-fib :
    {s t : fib f b} → (eq-Eq-fib-uncurry {s} {t} ∘ Eq-eq-fib {s} {t}) ~ id
  is-retraction-eq-Eq-fib refl = refl

  abstract
    is-equiv-Eq-eq-fib : {s t : fib f b} → is-equiv (Eq-eq-fib {s} {t})
    is-equiv-Eq-eq-fib =
      is-equiv-has-inverse
        eq-Eq-fib-uncurry
        is-section-eq-Eq-fib
        is-retraction-eq-Eq-fib

  equiv-Eq-eq-fib : {s t : fib f b} → (s ＝ t) ≃ Eq-fib s t
  pr1 equiv-Eq-eq-fib = Eq-eq-fib
  pr2 equiv-Eq-eq-fib = is-equiv-Eq-eq-fib

  abstract
    is-equiv-eq-Eq-fib :
      {s t : fib f b} → is-equiv (eq-Eq-fib-uncurry {s} {t})
    is-equiv-eq-Eq-fib =
      is-equiv-has-inverse
        Eq-eq-fib
        is-retraction-eq-Eq-fib
        is-section-eq-Eq-fib

  equiv-eq-Eq-fib : {s t : fib f b} → Eq-fib s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fib = eq-Eq-fib-uncurry
  pr2 equiv-eq-Eq-fib = is-equiv-eq-Eq-fib
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
  eq-Eq-fib-uncurry' {x , p} (refl , refl) =
    ap (pair x) (inv right-unit)

  eq-Eq-fib' :
    {s t : fib' f b} (α : pr1 s ＝ pr1 t) →
    (pr2 t) ＝ ((pr2 s) ∙ (ap f α)) → s ＝ t
  eq-Eq-fib' α β = eq-Eq-fib-uncurry' (α , β)

  is-section-eq-Eq-fib' :
    {s t : fib' f b} → (Eq-eq-fib' {s} {t} ∘ eq-Eq-fib-uncurry' {s} {t}) ~ id
  is-section-eq-Eq-fib' {x , refl} (refl , refl) = refl

  is-retraction-eq-Eq-fib' :
    {s t : fib' f b} → (eq-Eq-fib-uncurry' {s} {t} ∘ Eq-eq-fib' {s} {t}) ~ id
  is-retraction-eq-Eq-fib' {x , refl} refl = refl

  abstract
    is-equiv-Eq-eq-fib' : {s t : fib' f b} → is-equiv (Eq-eq-fib' {s} {t})
    is-equiv-Eq-eq-fib' =
      is-equiv-has-inverse
        eq-Eq-fib-uncurry'
        is-section-eq-Eq-fib'
        is-retraction-eq-Eq-fib'

  equiv-Eq-eq-fib' : {s t : fib' f b} → (s ＝ t) ≃ Eq-fib' s t
  pr1 equiv-Eq-eq-fib' = Eq-eq-fib'
  pr2 equiv-Eq-eq-fib' = is-equiv-Eq-eq-fib'

  abstract
    is-equiv-eq-Eq-fib' :
      {s t : fib' f b} → is-equiv (eq-Eq-fib-uncurry' {s} {t})
    is-equiv-eq-Eq-fib' =
      is-equiv-has-inverse
        Eq-eq-fib'
        is-retraction-eq-Eq-fib'
        is-section-eq-Eq-fib'

  equiv-eq-Eq-fib' : {s t : fib' f b} → Eq-fib' s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fib' = eq-Eq-fib-uncurry'
  pr2 equiv-eq-Eq-fib' = is-equiv-eq-Eq-fib'
```

### `fib f y` and `fib' f y` are equivalent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  map-equiv-fib : fib f y → fib' f y
  pr1 (map-equiv-fib (x , refl)) = x
  pr2 (map-equiv-fib (x , refl)) = refl

  map-inv-equiv-fib : fib' f y → fib f y
  pr1 (map-inv-equiv-fib (x , refl)) = x
  pr2 (map-inv-equiv-fib (x , refl)) = refl

  is-section-map-inv-equiv-fib : (map-equiv-fib ∘ map-inv-equiv-fib) ~ id
  is-section-map-inv-equiv-fib (x , refl) = refl

  is-retraction-map-inv-equiv-fib : (map-inv-equiv-fib ∘ map-equiv-fib) ~ id
  is-retraction-map-inv-equiv-fib (x , refl) = refl

  is-equiv-map-equiv-fib : is-equiv map-equiv-fib
  is-equiv-map-equiv-fib =
    is-equiv-has-inverse
      map-inv-equiv-fib
      is-section-map-inv-equiv-fib
      is-retraction-map-inv-equiv-fib

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
  map-fib-pr1 ((x , y) , p) = tr B p y

  map-inv-fib-pr1 : B a → fib (pr1 {B = B}) a
  pr1 (pr1 (map-inv-fib-pr1 b)) = a
  pr2 (pr1 (map-inv-fib-pr1 b)) = b
  pr2 (map-inv-fib-pr1 b) = refl

  is-section-map-inv-fib-pr1 : (map-inv-fib-pr1 ∘ map-fib-pr1) ~ id
  is-section-map-inv-fib-pr1 ((.a , y) , refl) = refl

  is-retraction-map-inv-fib-pr1 : (map-fib-pr1 ∘ map-inv-fib-pr1) ~ id
  is-retraction-map-inv-fib-pr1 b = refl

  abstract
    is-equiv-map-fib-pr1 : is-equiv map-fib-pr1
    is-equiv-map-fib-pr1 =
      is-equiv-has-inverse
        map-inv-fib-pr1
        is-retraction-map-inv-fib-pr1
        is-section-map-inv-fib-pr1

  equiv-fib-pr1 : fib (pr1 {B = B}) a ≃ B a
  pr1 equiv-fib-pr1 = map-fib-pr1
  pr2 equiv-fib-pr1 = is-equiv-map-fib-pr1

  abstract
    is-equiv-map-inv-fib-pr1 : is-equiv map-inv-fib-pr1
    is-equiv-map-inv-fib-pr1 =
      is-equiv-has-inverse
        map-fib-pr1
        is-section-map-inv-fib-pr1
        is-retraction-map-inv-fib-pr1

  inv-equiv-fib-pr1 : B a ≃ fib (pr1 {B = B}) a
  pr1 inv-equiv-fib-pr1 = map-inv-fib-pr1
  pr2 inv-equiv-fib-pr1 = is-equiv-map-inv-fib-pr1
```

### The total space of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fib : (Σ B (fib f)) → A
  map-equiv-total-fib t = pr1 (pr2 t)

  triangle-map-equiv-total-fib : pr1 ~ (f ∘ map-equiv-total-fib)
  triangle-map-equiv-total-fib t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fib : A → Σ B (fib f)
  pr1 (map-inv-equiv-total-fib x) = f x
  pr1 (pr2 (map-inv-equiv-total-fib x)) = x
  pr2 (pr2 (map-inv-equiv-total-fib x)) = refl

  is-retraction-map-inv-equiv-total-fib :
    (map-inv-equiv-total-fib ∘ map-equiv-total-fib) ~ id
  is-retraction-map-inv-equiv-total-fib (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fib :
    (map-equiv-total-fib ∘ map-inv-equiv-total-fib) ~ id
  is-section-map-inv-equiv-total-fib x = refl

  abstract
    is-equiv-map-equiv-total-fib : is-equiv map-equiv-total-fib
    is-equiv-map-equiv-total-fib =
      is-equiv-has-inverse
        map-inv-equiv-total-fib
        is-section-map-inv-equiv-total-fib
        is-retraction-map-inv-equiv-total-fib

    is-equiv-map-inv-equiv-total-fib : is-equiv map-inv-equiv-total-fib
    is-equiv-map-inv-equiv-total-fib =
      is-equiv-has-inverse
        map-equiv-total-fib
        is-retraction-map-inv-equiv-total-fib
        is-section-map-inv-equiv-total-fib

  equiv-total-fib : Σ B (fib f) ≃ A
  pr1 equiv-total-fib = map-equiv-total-fib
  pr2 equiv-total-fib = is-equiv-map-equiv-total-fib

  inv-equiv-total-fib : A ≃ Σ B (fib f)
  pr1 inv-equiv-total-fib = map-inv-equiv-total-fib
  pr2 inv-equiv-total-fib = is-equiv-map-inv-equiv-total-fib
```

### Fibers of compositions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (x : X)
  where

  map-compute-fib-comp :
    fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
  pr1 (pr1 (map-compute-fib-comp (a , p))) = h a
  pr2 (pr1 (map-compute-fib-comp (a , p))) = p
  pr1 (pr2 (map-compute-fib-comp (a , p))) = a
  pr2 (pr2 (map-compute-fib-comp (a , p))) = refl

  inv-map-compute-fib-comp :
    Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
  pr1 (inv-map-compute-fib-comp t) = pr1 (pr2 t)
  pr2 (inv-map-compute-fib-comp t) =
    ap g (pr2 (pr2 t)) ∙ pr2 (pr1 t)

  is-section-inv-map-compute-fib-comp :
    (map-compute-fib-comp ∘ inv-map-compute-fib-comp) ~ id
  is-section-inv-map-compute-fib-comp
    ((.(h a) , refl) , (a , refl)) = refl

  is-retraction-inv-map-compute-fib-comp :
    (inv-map-compute-fib-comp ∘ map-compute-fib-comp) ~ id
  is-retraction-inv-map-compute-fib-comp (a , refl) = refl

  abstract
    is-equiv-map-compute-fib-comp :
      is-equiv map-compute-fib-comp
    is-equiv-map-compute-fib-comp =
      is-equiv-has-inverse
        ( inv-map-compute-fib-comp)
        ( is-section-inv-map-compute-fib-comp)
        ( is-retraction-inv-map-compute-fib-comp)

  equiv-compute-fib-comp :
    fib (g ∘ h) x ≃ Σ (fib g x) (λ t → fib h (pr1 t))
  pr1 equiv-compute-fib-comp = map-compute-fib-comp
  pr2 equiv-compute-fib-comp = is-equiv-map-compute-fib-comp

  abstract
    is-equiv-inv-map-compute-fib-comp :
      is-equiv inv-map-compute-fib-comp
    is-equiv-inv-map-compute-fib-comp =
        is-equiv-has-inverse
          ( map-compute-fib-comp)
          ( is-retraction-inv-map-compute-fib-comp)
          ( is-section-inv-map-compute-fib-comp)

  inv-equiv-compute-fib-comp :
    Σ (fib g x) (λ t → fib h (pr1 t)) ≃ fib (g ∘ h) x
  pr1 inv-equiv-compute-fib-comp = inv-map-compute-fib-comp
  pr2 inv-equiv-compute-fib-comp = is-equiv-inv-map-compute-fib-comp
```

### When a product is taken over all fibers of a map, then we can equivalently take the product over the domain of that map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3)
  where

  map-reduce-Π-fib :
    ((y : B) (z : fib f y) → C y z) → ((x : A) → C (f x) (x , refl))
  map-reduce-Π-fib h x = h (f x) (x , refl)

  inv-map-reduce-Π-fib :
    ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fib f y) → C y z)
  inv-map-reduce-Π-fib h .(f x) (x , refl) = h x

  is-section-inv-map-reduce-Π-fib :
    (map-reduce-Π-fib ∘ inv-map-reduce-Π-fib) ~ id
  is-section-inv-map-reduce-Π-fib h = refl

  is-retraction-inv-map-reduce-Π-fib' :
    (h : (y : B) (z : fib f y) → C y z) (y : B) →
    (inv-map-reduce-Π-fib (map-reduce-Π-fib h) y) ~ (h y)
  is-retraction-inv-map-reduce-Π-fib' h .(f z) (z , refl) = refl

  is-retraction-inv-map-reduce-Π-fib :
    (inv-map-reduce-Π-fib ∘ map-reduce-Π-fib) ~ id
  is-retraction-inv-map-reduce-Π-fib h =
    eq-htpy (eq-htpy ∘ is-retraction-inv-map-reduce-Π-fib' h)

  is-equiv-map-reduce-Π-fib : is-equiv map-reduce-Π-fib
  is-equiv-map-reduce-Π-fib =
    is-equiv-has-inverse
      ( inv-map-reduce-Π-fib)
      ( is-section-inv-map-reduce-Π-fib)
      ( is-retraction-inv-map-reduce-Π-fib)

  reduce-Π-fib' :
    ((y : B) (z : fib f y) → C y z) ≃ ((x : A) → C (f x) (x , refl))
  pr1 reduce-Π-fib' = map-reduce-Π-fib
  pr2 reduce-Π-fib' = is-equiv-map-reduce-Π-fib

reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fib f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fib f C = reduce-Π-fib' f (λ y z → C y)
```
