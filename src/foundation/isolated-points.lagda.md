# Isolated points

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.isolated-points where

open import foundation.constant-maps using (const; fib-const)
open import foundation.contractible-types using (is-contr; is-contr-equiv)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-embeddings using (_↪d_)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-equiv; is-decidable-equiv';
    is-prop-is-decidable; is-decidable-prod; is-decidable-unit)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; is-emb-comp')
open import foundation.empty-types using (empty; is-prop-empty; ex-falso)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; refl; tr; ap)
open import foundation.injective-maps using (is-emb-is-injective)
open import foundation.propositions using
  ( is-prop; is-prop-equiv; is-proof-irrelevant-is-prop; UU-Prop;
    is-prop-is-inhabited; is-prop-Π)
open import foundation.sets using (is-set)
open import foundation.subtypes using (eq-subtype; is-emb-pr1; equiv-ap-pr1)
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

  Eq-isolated-point-Prop : is-isolated a → A → UU-Prop lzero
  pr1 (Eq-isolated-point-Prop d x) = Eq-isolated-point d x
  pr2 (Eq-isolated-point-Prop d x) = is-prop-Eq-isolated-point d x

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
        ( Eq-isolated-point-Prop d)
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

### Being an isolated point is a property

```agda
is-prop-is-isolated :
  {l1 : Level} {A : UU l1} (a : A) → is-prop (is-isolated a)
is-prop-is-isolated a =
  is-prop-is-inhabited
    ( λ H →
      is-prop-Π (λ x → is-prop-is-decidable (is-prop-eq-isolated-point a H x)))

inclusion-isolated-point :
  {l1 : Level} (A : UU l1) → isolated-point A → A
inclusion-isolated-point A = pr1

is-emb-inclusion-isolated-point :
  {l1 : Level} (A : UU l1) → is-emb (inclusion-isolated-point A)
is-emb-inclusion-isolated-point A = is-emb-pr1 is-prop-is-isolated

has-decidable-equality-isolated-point :
  {l1 : Level} (A : UU l1) → has-decidable-equality (isolated-point A)
has-decidable-equality-isolated-point A (pair x dx) (pair y dy) =
  is-decidable-equiv
    ( equiv-ap-pr1 is-prop-is-isolated)
    ( dx y)

is-set-isolated-point :
  {l1 : Level} (A : UU l1) → is-set (isolated-point A)
is-set-isolated-point A =
  is-set-has-decidable-equality (has-decidable-equality-isolated-point A)

decidable-emb-isolated-point :
  {l1 : Level} {A : UU l1} (a : isolated-point A) → unit ↪d A
decidable-emb-isolated-point {l1} {A} a =
  pair
    ( const unit A (pr1 a))
    ( pair
      ( is-emb-comp'
        ( inclusion-isolated-point A)
        ( const unit (isolated-point A) a)
        ( is-emb-inclusion-isolated-point A)
        ( is-emb-is-injective
          ( is-set-isolated-point A)
           λ { {star} {star} p → refl}))
      ( λ x → is-decidable-prod is-decidable-unit (pr2 a x)))
```
