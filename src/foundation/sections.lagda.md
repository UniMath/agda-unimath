---
title: Sections
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.sections where

open import foundation-core.sections public

open import foundation-core.retractions using (_retract-of_)

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path'; is-contr-Π)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-right-factor; is-equiv-id; _≃_; is-equiv-left-factor;
    _∘e_; id-equiv; map-inv-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using
  ( _~_; refl-htpy; _·l_; _∙h_; _·r_; inv-htpy; inv-htpy-assoc-htpy;
    ap-concat-htpy'; left-inv-htpy)
open import foundation.identity-types using (_＝_; refl; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-equiv-pr1-is-contr; is-contr-is-equiv-pr1; left-unit-law-Σ-is-contr;
    equiv-right-swap-Σ)
open import foundation.type-theoretic-principle-of-choice using
  ( Π-total-fam; inv-distributive-Π-Σ; distributive-Π-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import foundation-core.fibers-of-maps using (fib; equiv-total-fib)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-Σ)
```

## Idea

Any dependent function induces a section of the projection map

## Properties

### Sections of the projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section b a) = a
  pr2 (map-section b a) = b a

  htpy-map-section :
    (b : (x : A) → B x) → (pr1 ∘ map-section b) ~ id
  htpy-map-section b a = refl

  sec-dependent-function : ((x : A) → B x) → sec (pr1 {B = B})
  pr1 (sec-dependent-function b) = map-section b
  pr2 (sec-dependent-function b) = htpy-map-section b
```

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-map-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → is-equiv (map-section b)
  is-equiv-map-section b C =
    is-equiv-right-factor
      ( id)
      ( pr1)
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-pr1-is-contr C)
      ( is-equiv-id)

  equiv-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → A ≃ Σ A B
  equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

  is-contr-fam-is-equiv-map-section :
    (b : (x : A) → B x) → is-equiv (map-section b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section b H =
    is-contr-is-equiv-pr1
      ( is-equiv-left-factor id pr1
        ( map-section b)
        ( htpy-map-section b)
        ( is-equiv-id)
        ( H))
```

```agda
equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)
```

### Any section of a type family is an injective map

```agda
is-injective-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section b)
is-injective-map-section b = ap pr1
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-sec-pr1 : sec (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-sec-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → y ＝ x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
```

### Extensionality of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  htpy-sec : (s t : sec f) → UU (l1 ⊔ l2)
  htpy-sec s t = Σ (pr1 s ~ pr1 t) (λ H → pr2 s ~ ((f ·l H) ∙h pr2 t))

  extensionality-sec : (s t : sec f) → (s ＝ t) ≃ htpy-sec s t
  extensionality-sec (pair s H) =
    extensionality-Σ
      ( λ {s'} H' K → H ~ ((f ·l K) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ s' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-sec :
    (s t : sec f)
    (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) → s ＝ t
  eq-htpy-sec s t H K =
    map-inv-equiv (extensionality-sec s t) (pair H K)
```

### If the right factor of a composite has a section, then the type of sections of the left factor is a retract of the type of sections of the composite.

```agda
isretr-section-comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (sec-h : sec h) →
  ((section-left-factor-htpy f g h H) ∘ (section-comp-htpy f g h H sec-h)) ~ id
isretr-section-comp-htpy f g h H (pair k K) (pair l L) =
  eq-htpy-sec
    ( ( section-left-factor-htpy f g h H ∘
        section-comp-htpy f g h H (pair k K))
      ( pair l L))
    ( pair l L)
    ( K ·r l)
    ( ( inv-htpy-assoc-htpy
        ( inv-htpy (H ·r (k ∘ l)))
        ( H ·r (k ∘ l))
        ( (g ·l (K ·r l)) ∙h L)) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy (H ·r (k ∘ l))) ∙h (H ·r (k ∘ l)))
        ( refl-htpy)
        ( (g ·l (K ·r l)) ∙h L)
        ( left-inv-htpy (H ·r (k ∘ l)))))

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
pr1 (sec-left-factor-retract-of-sec-composition f g h H sec-h) =
  section-comp-htpy f g h H sec-h
pr1 (pr2 (sec-left-factor-retract-of-sec-composition f g h H sec-h)) =
  section-left-factor-htpy f g h H
pr2 (pr2 (sec-left-factor-retract-of-sec-composition f g h H sec-h)) =
  isretr-section-comp-htpy f g h H sec-h
```
