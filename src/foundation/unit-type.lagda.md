---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.unit-type where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; center; contraction)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (const; _∘_; id)
open import foundation.equivalences using (is-equiv; _≃_; is-equiv-has-inverse)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl)
open import foundation.levels using (Level; lzero; UU)
open import foundation.propositions using (is-prop; is-prop-is-contr; UU-Prop)
open import foundation.raising-universe-levels using
  ( raise; equiv-raise; map-raise)
```

## The unit type

```agda
data unit : UU lzero where
  star : unit

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star
```

```agda
abstract
  is-contr-unit : is-contr unit
  pr1 is-contr-unit = star
  pr2 is-contr-unit star = refl
```

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-terminal-map-is-contr :
      is-contr A → is-equiv (terminal-map {A = A})
    pr1 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit (center H)
    pr2 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit refl
    pr1 (pr2 (is-equiv-terminal-map-is-contr H)) = const unit A (center H)
    pr2 (pr2 (is-equiv-terminal-map-is-contr H)) = contraction H

  abstract
    is-contr-is-equiv-const : is-equiv (terminal-map {A = A}) → is-contr A
    pr1 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = h star
    pr2 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = isretr
```

```agda
abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
pr1 unit-Prop = unit
pr2 unit-Prop = is-prop-unit
```

```agda
raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit
```

## Left unit law for dependent pair types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Σ : Σ unit A → A star
  map-left-unit-law-Σ (pair star a) = a

  map-inv-left-unit-law-Σ : A star → Σ unit A
  pr1 (map-inv-left-unit-law-Σ a) = star
  pr2 (map-inv-left-unit-law-Σ a) = a

  issec-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  issec-map-inv-left-unit-law-Σ a = refl

  isretr-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  isretr-map-inv-left-unit-law-Σ (pair star a) = refl

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ =
    is-equiv-has-inverse
      map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ

  left-unit-law-Σ : Σ unit A ≃ A star
  pr1 left-unit-law-Σ = map-left-unit-law-Σ
  pr2 left-unit-law-Σ = is-equiv-map-left-unit-law-Σ
  
  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ =
    is-equiv-has-inverse
      map-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  pr1 inv-left-unit-law-Σ = map-inv-left-unit-law-Σ
  pr2 inv-left-unit-law-Σ = is-equiv-map-inv-left-unit-law-Σ
```

## Left unit law for cartesian products

```agda
module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-prod : unit × A → A
  map-left-unit-law-prod = pr2

  map-inv-left-unit-law-prod : A → unit × A
  map-inv-left-unit-law-prod = map-inv-left-unit-law-Σ (λ x → A)

  issec-map-inv-left-unit-law-prod :
    ( map-left-unit-law-prod ∘ map-inv-left-unit-law-prod) ~ id
  issec-map-inv-left-unit-law-prod =
    issec-map-inv-left-unit-law-Σ (λ x → A)

  isretr-map-inv-left-unit-law-prod :
    ( map-inv-left-unit-law-prod ∘ map-left-unit-law-prod) ~ id
  isretr-map-inv-left-unit-law-prod (pair star a) = refl

  is-equiv-map-left-unit-law-prod : is-equiv map-left-unit-law-prod
  is-equiv-map-left-unit-law-prod =
    is-equiv-has-inverse
      map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod

  left-unit-law-prod : (unit × A) ≃ A
  pr1 left-unit-law-prod = map-left-unit-law-prod
  pr2 left-unit-law-prod = is-equiv-map-left-unit-law-prod

  is-equiv-map-inv-left-unit-law-prod : is-equiv map-inv-left-unit-law-prod
  is-equiv-map-inv-left-unit-law-prod =
    is-equiv-has-inverse
      map-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod

  inv-left-unit-law-prod : A ≃ (unit × A)
  pr1 inv-left-unit-law-prod = map-inv-left-unit-law-prod
  pr2 inv-left-unit-law-prod = is-equiv-map-inv-left-unit-law-prod

  map-right-unit-law-prod : A × unit → A
  map-right-unit-law-prod = pr1

  map-inv-right-unit-law-prod : A → A × unit
  pr1 (map-inv-right-unit-law-prod a) = a
  pr2 (map-inv-right-unit-law-prod a) = star

  issec-map-inv-right-unit-law-prod :
    (map-right-unit-law-prod ∘ map-inv-right-unit-law-prod) ~ id
  issec-map-inv-right-unit-law-prod a = refl

  isretr-map-inv-right-unit-law-prod :
    (map-inv-right-unit-law-prod ∘ map-right-unit-law-prod) ~ id
  isretr-map-inv-right-unit-law-prod (pair a star) = refl

  is-equiv-map-right-unit-law-prod : is-equiv map-right-unit-law-prod
  is-equiv-map-right-unit-law-prod =
    is-equiv-has-inverse
      map-inv-right-unit-law-prod
      issec-map-inv-right-unit-law-prod
      isretr-map-inv-right-unit-law-prod

  right-unit-law-prod : (A × unit) ≃ A
  pr1 right-unit-law-prod = map-right-unit-law-prod
  pr2 right-unit-law-prod = is-equiv-map-right-unit-law-prod
```
