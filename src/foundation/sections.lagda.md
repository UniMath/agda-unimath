# Sections of type families

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.sections where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path'; is-contr-Π)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs using
  ( Π-total-fam; inv-distributive-Π-Σ; distributive-Π-Σ)
open import foundation.equivalences using
  ( is-equiv; is-equiv-right-factor; is-equiv-id; _≃_; is-equiv-left-factor;
    sec; _∘e_; id-equiv; map-inv-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-Σ)
open import foundation.homotopies using (_~_; refl-htpy; _·l_; _∙h_)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-right-swap-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-equiv-pr1-is-contr; is-contr-is-equiv-pr1; left-unit-law-Σ-is-contr)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Any dependent function induces a section of the projection map

## Definition

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
```

## Properties

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
          ( Π-total-fam (λ x y → Id y x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  htpy-sec : (s t : sec f) → UU (l1 ⊔ l2)
  htpy-sec s t = Σ (pr1 s ~ pr1 t) (λ H → pr2 s ~ ((f ·l H) ∙h pr2 t))

  extensionality-sec : (s t : sec f) → Id s t ≃ htpy-sec s t
  extensionality-sec (pair s H) =
    extensionality-Σ
      ( λ {s'} H' K → H ~ ((f ·l K) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ s' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-sec :
    (s t : sec f)
    (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) → Id s t
  eq-htpy-sec s t H K =
    map-inv-equiv (extensionality-sec s t) (pair H K)

{-
  refl-htpy-sec : (s : sec f) → htpy-sec s s
  pr1 (refl-htpy-sec s) = refl-htpy
  pr2 (refl-htpy-sec s) = refl-htpy

  htpy-eq-sec : (s t : sec f) → Id s t → htpy-sec s t
  htpy-eq-sec s .s refl = refl-htpy-sec s

  abstract
    is-contr-total-htpy-sec : (s : sec f) → is-contr (Σ (sec f) (htpy-sec s))
    is-contr-total-htpy-sec s =
      is-contr-total-Eq-structure
        ( λ g G H → pr2 s ~ ((f ·l H) ∙h G))
        ( is-contr-total-htpy (pr1 s))
        ( pair (pr1 s) refl-htpy)
        ( is-contr-total-htpy (pr2 s))
  abstract
    is-equiv-htpy-eq-sec :
      (s t : sec f) → is-equiv (htpy-eq-sec s t)
    is-equiv-htpy-eq-sec s =
      fundamental-theorem-id s
        ( refl-htpy-sec s)
        ( is-contr-total-htpy-sec s)
        ( htpy-eq-sec s)

  equiv-htpy-eq-sec : (s t : sec f) → Id s t ≃ htpy-sec s t
  pr1 (equiv-htpy-eq-sec s t) = htpy-eq-sec s t
  pr2 (equiv-htpy-eq-sec s t) = is-equiv-htpy-eq-sec s t

eq-htpy-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (s t : sec f) →
  (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) →
  Id s t
eq-htpy-sec {f = f} s t H K =
  map-inv-is-equiv (is-equiv-htpy-eq-sec f s t) (pair H K)
  -}
```
