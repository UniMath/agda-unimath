# Isolated points

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.isolated-points where

open import foundation.constant-maps using (const; fib-const)
open import foundation.contractible-types using (is-contr; is-contr-equiv)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using (has-decidable-equality)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-equiv; is-decidable-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.empty-types using (empty; is-prop-empty; ex-falso)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; refl; tr; ap)
open import foundation.propositions using
  ( is-prop; is-prop-equiv; is-proof-irrelevant-is-prop)
open import foundation.subtypes using (eq-subtype)
open import foundation.type-arithmetic-unit-type using
  ( left-unit-law-prod)
open import foundation.unit-type using (unit; is-prop-unit; star)
open import foundation.universe-levels using (Level; UU; _⊔_; lzero)
```

## Idea

A point `a : A` is considered to be isolated if `Id a x` is decidable for any `x`.

## Definition

```agda
is-isolated :
  {l1 : Level} {X : UU l1} (a : X) → UU l1
is-isolated {l1} {X} a = (x : X) → is-decidable (Id a x)

isolated-point :
  {l1 : Level} (X : UU l1) → UU l1
isolated-point X = Σ X is-isolated
```

## Properties

### A point is decidable if and only if the constant map pointing at it is decidable

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where
  
  is-decidable-map-const-is-isolated :
    is-isolated a → is-decidable-map (const unit A a)
  is-decidable-map-const-is-isolated d x =
    is-decidable-equiv (fib-const a x) (d x)

  is-isolated-is-decidable-map-const :
    is-decidable-map (const unit A a) → is-isolated a
  is-isolated-is-decidable-map-const d x =
    is-decidable-equiv' (fib-const a x) (d x)

  cases-Eq-isolated-point :
    is-isolated a → (x : A) → is-decidable (Id a x) → UU lzero
  cases-Eq-isolated-point H x (inl p) = unit
  cases-Eq-isolated-point H x (inr f) = empty

  abstract
    is-prop-cases-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (Id a x)) →
      is-prop (cases-Eq-isolated-point d x dx)
    is-prop-cases-Eq-isolated-point d x (inl p) = is-prop-unit
    is-prop-cases-Eq-isolated-point d x (inr f) = is-prop-empty

  Eq-isolated-point : is-isolated a → A → UU lzero
  Eq-isolated-point d x = cases-Eq-isolated-point d x (d x)

  abstract
    is-prop-Eq-isolated-point :
      (d : is-isolated a) (x : A) → is-prop (Eq-isolated-point d x)
    is-prop-Eq-isolated-point d x =
      is-prop-cases-Eq-isolated-point d x (d x)

  decide-reflexivity :
    (d : is-decidable (Id a a)) → Σ (Id a a) (λ p → Id (inl p) d)
  pr1 (decide-reflexivity (inl p)) = p
  pr2 (decide-reflexivity (inl p)) = refl
  decide-reflexivity (inr f) = ex-falso (f refl)

  abstract
    refl-Eq-isolated-point : (d : is-isolated a) → Eq-isolated-point d a
    refl-Eq-isolated-point d =
      tr ( cases-Eq-isolated-point d a)
        ( pr2 (decide-reflexivity (d a)))
        ( star)

  abstract
    Eq-eq-isolated-point :
      (d : is-isolated a) {x : A} → Id a x → Eq-isolated-point d x
    Eq-eq-isolated-point d refl = refl-Eq-isolated-point d

  abstract
    center-total-Eq-isolated-point :
      (d : is-isolated a) → Σ A (Eq-isolated-point d)
    pr1 (center-total-Eq-isolated-point d) = a
    pr2 (center-total-Eq-isolated-point d) = refl-Eq-isolated-point d
  
    cases-contraction-total-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (Id a x))
      (e : cases-Eq-isolated-point d x dx) → Id a x
    cases-contraction-total-Eq-isolated-point d x (inl p) e = p
  
    contraction-total-Eq-isolated-point :
      (d : is-isolated a) (t : Σ A (Eq-isolated-point d)) →
      Id (center-total-Eq-isolated-point d) t
    contraction-total-Eq-isolated-point d (pair x e) =
      eq-subtype
        ( is-prop-Eq-isolated-point d)
        ( cases-contraction-total-Eq-isolated-point d x (d x) e)

    is-contr-total-Eq-isolated-point :
      (d : is-isolated a) → is-contr (Σ A (Eq-isolated-point d))
    pr1 (is-contr-total-Eq-isolated-point d) = center-total-Eq-isolated-point d
    pr2 (is-contr-total-Eq-isolated-point d) =
      contraction-total-Eq-isolated-point d

  abstract
    is-equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → is-equiv (Eq-eq-isolated-point d {x})
    is-equiv-Eq-eq-isolated-point d =
      fundamental-theorem-id a
        ( refl-Eq-isolated-point d)
        ( is-contr-total-Eq-isolated-point d)
        ( λ x → Eq-eq-isolated-point d {x})

  abstract
    equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → Id a x ≃ Eq-isolated-point d x
    pr1 (equiv-Eq-eq-isolated-point d x) = Eq-eq-isolated-point d
    pr2 (equiv-Eq-eq-isolated-point d x) = is-equiv-Eq-eq-isolated-point d x

  abstract
    is-prop-eq-isolated-point : (d : is-isolated a) (x : A) → is-prop (Id a x)
    is-prop-eq-isolated-point d x =
      is-prop-equiv
        ( equiv-Eq-eq-isolated-point d x)
        ( is-prop-Eq-isolated-point d x)

  abstract
    is-emb-const-is-isolated : is-isolated a → is-emb (const unit A a)
    is-emb-const-is-isolated d star =
      fundamental-theorem-id star
        refl
        ( is-contr-equiv
          ( Id a a)
          ( left-unit-law-prod)
          ( is-proof-irrelevant-is-prop
            ( is-prop-eq-isolated-point d a)
            ( refl)))
        ( λ x → ap (λ y → a))
```
