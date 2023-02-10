---
title: Transport
---

```agda
module foundation.transport where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.universal-property-dependent-pair-types
```

## Properties

### Transport in a family of cartesian products

```agda
tr-prod :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A}
  (B C : A → UU l2) (p : a0 ＝ a1) (u : B a0 × C a0) →
  (tr (λ a → B a × C a) p u) ＝ (pair (tr B p (pr1 u)) (tr C p (pr2 u)))
tr-prod B C refl u = refl
```

### Transport in a family over a cartesian product

#### Computing transport along a path of the form `eq-pair`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where
  
  tr-eq-pair :
    (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    tr C (eq-pair p q) u ＝
    tr (λ x → C (a1 , x)) q (tr (λ x → C (x , b0)) p u)
  tr-eq-pair C refl refl u = refl
```

#### Computing transport along a path of the form `eq-pair` When one of the paths is `refl`

```agda
  left-unit-law-tr-eq-pair :
    (C : A × B → UU l3) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr C (eq-pair refl q) u) ＝ tr (λ x → C (a0 , x)) q u
  left-unit-law-tr-eq-pair C refl u = refl

  right-unit-law-tr-eq-pair :
    (C : A × B → UU l3) (p : a0 ＝ a1) (u : C (a0 , b0)) →
    (tr C (eq-pair p refl) u) ＝ tr (λ x → C (x , b0)) p u
  right-unit-law-tr-eq-pair C refl u = refl
```

#### Computing transport along a path of the form `eq-pair` when both paths are identical

```agda
tr-eq-pair-diagonal :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (C : A × A → UU l2)
  (p : a0 ＝ a1) (u : C (a0 , a0)) → (tr C (eq-pair p p) u) ＝ (tr (λ a → C (a , a)) p u)
tr-eq-pair-diagonal C refl u = refl
```

### Transport in a family of dependent pair types

```agda
tr-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (z : Σ (B a0) (λ x → C a0 x)) →
  tr (λ a → (Σ (B a) (C a))) p z ＝
  pair (tr B p (pr1 z)) (tr (ind-Σ C) (eq-pair-Σ p refl) (pr2 z))
tr-Σ C refl z = refl
```

### Transport in a family over a dependent pair type

```agda
tr-eq-pair-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}
  {B : A → UU l2} {b0 : B a0} {b1 : B a1} (C : (Σ A (λ a → B a)) → UU l3)
  (p : a0 ＝ a1) (q : path-over (B) p b0 b1) (u : C (a0 , b0)) →
  tr C (eq-pair-Σ p q) u ＝
  tr (λ x → C (a1 , x)) q (tr C (eq-pair-Σ p refl) u)
tr-eq-pair-Σ C refl refl u = refl
```

### Transport in a family of function types

```agda
tr-function-type :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (C : A → UU l3)
  (p : a0 ＝ a1) (f : B a0 → C a0) →
  tr (λ a → B a → C a) p f ＝ λ x → tr C p (f (tr B (inv p) x))
tr-function-type B C refl f = refl
```

#### This implies implies a charaterization of dependent paths in a family of function types

```agda

extensionality-path-over-function-type :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (C : A → UU l3)
  (p : a0 ＝ a1) {f : B a0 → C a0} {g : B a1 → C a1} →
  (path-over (λ a → B a → C a) p f g) ≃ (((tr C p) ∘ f) ~ (g ∘ (tr B p)))
extensionality-path-over-function-type {a1 = a1} B C p {f = f} {g = g} =
  equiv-funext ∘e
  ((inv-equiv (equiv-concat (eq-htpy (λ a → ap (λ t → tr C p (f t)) (isretr-inv-tr B p a))) (g ∘ (tr B p)))) ∘e
  ((equiv-ap (equiv-precomp (equiv-tr B p ) (C a1)) (λ x → tr C p (f (tr B (inv p) x))) g) ∘e
  (inv-equiv (equiv-concat (tr-function-type B C p f) g))))

coh-sq-path-over-function-type :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (C : A → UU l3)
  (p : a0 ＝ a1) {f : B a0 → C a0} {g : B a1 → C a1} →
  (path-over (λ a → B a → C a) p f g) → (((tr C p) ∘ f) ~ (g ∘ (tr B p)))
coh-sq-path-over-function-type B C p =
  map-equiv (extensionality-path-over-function-type B C p)

path-over-function-type-coh-sq :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (C : A → UU l3)
  (p : a0 ＝ a1) {f : B a0 → C a0} {g : B a1 → C a1} →
  (((tr C p) ∘ f) ~ (g ∘ (tr B p))) → (path-over (λ a → B a → C a) p f g)
path-over-function-type-coh-sq B C p =
  map-inv-equiv (extensionality-path-over-function-type B C p)
```

### Transport in families of identity types

```agda
tr-fx＝gy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {a0 a1 : A} {b0 b1 : B} (f : A → C) (g : B → C)
  (p : a0 ＝ a1) (q : b0 ＝ b1) (s : f a0 ＝ g b0) → 
  (tr (λ z → (f (pr1 z)) ＝ (g (pr2 z))) (eq-pair p q) s) ＝
  (((inv (ap f p)) ∙ s) ∙ (ap g q))
tr-fx＝gy f g refl refl s = inv right-unit

tr-x＝y :
  {l1 : Level} {A : UU l1} {a0 a1 a2 a3 : A}
  (p : a0 ＝ a1) (q : a2 ＝ a3) (s : a0 ＝ a2) → 
  (tr (λ z → (pr1 z) ＝ (pr2 z)) (eq-pair p q) s) ＝ ((inv p) ∙ (s ∙ q))
tr-x＝y refl refl s = inv right-unit

tr-fx＝gx :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  {a0 a1 : A} (p : a0 ＝ a1) (q : f a0 ＝ g a0) → (tr (λ x → f x ＝ g x) p q) ＝((inv (ap f p) ∙ q) ∙ (ap g p))
tr-fx＝gx f g p q = inv (tr-eq-pair-diagonal (λ z → f (pr1 z) ＝ g (pr2 z)) p q) ∙ (tr-fx＝gy f g p p q)
```

#### This implies a characterization of dependent paths in a family of identity types

```agda
extensionality-path-over-fx＝gx :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  {a0 a1 : A} (p : a0 ＝ a1) (q : f a0 ＝ g a0) (q' : f a1 ＝ g a1) →
  ((tr (λ x → f x ＝ g x) p q) ＝ q') ≃ ((q ∙ (ap g p)) ＝ ((ap f p) ∙ q'))
extensionality-path-over-fx＝gx f g p q q' =
  equiv-concat' (q ∙ ap g p)  (ap (λ t → t ∙ q') (inv-inv (ap f p))) ∘e
  ((equiv-inv-con (inv (ap f p)) (q ∙ ap g p) q') ∘e
  ((equiv-concat (inv (assoc  (inv (ap f p)) q (ap g p))) q') ∘e
  (equiv-concat (inv (tr-fx＝gx f g p q)) q')))

nat-sq-path-over-fx＝gx :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  {a0 a1 : A} (p : a0 ＝ a1) (q : f a0 ＝ g a0) (q' : f a1 ＝ g a1) →
  ((tr (λ x → f x ＝ g x) p q) ＝ q') → ((q ∙ (ap g p)) ＝ ((ap f p) ∙ q'))
nat-sq-path-over-fx＝gx f g p q q' =
  map-equiv (extensionality-path-over-fx＝gx f g p q q')
```

### Transport in the family of loops

```agda
tr-loop :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (p : a0 ＝ a1) (l : a0 ＝ a0) →
  (tr (λ y → y ＝ y) p l) ＝ (((inv p) ∙ l) ∙ p)
tr-loop refl l = inv right-unit
```
