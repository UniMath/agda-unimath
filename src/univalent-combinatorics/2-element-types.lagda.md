# 2-element types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-types where

open import elementary-number-theory.equality-natural-numbers using
  ( Eq-eq-ℕ)
open import elementary-number-theory.equality-standard-finite-types using
  ( Eq-Fin-eq)
open import elementary-number-theory.standard-finite-types using
  ( Fin; zero-Fin; equiv-succ-Fin; one-Fin; raise-Fin; equiv-raise-Fin;
    is-not-contractible-Fin)

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-equiv; is-prop-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.double-negation using (dn-Prop'; intro-dn)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using
  ( _≃_; map-equiv; id-equiv; htpy-equiv; eq-htpy-equiv; is-equiv;
    is-equiv-has-inverse; is-equiv-Prop; is-equiv-left-factor';
    equiv-postcomp-equiv; is-equiv-comp; is-equiv-map-equiv;
    is-equiv-comp-equiv; _∘e_; equiv-precomp-equiv; map-inv-equiv; inv-equiv)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.mere-equivalences using (mere-equiv; mere-equiv-Prop)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.raising-universe-levels using (map-raise)
open import foundation.subuniverses using (is-contr-total-equiv-subuniverse)
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coprod-is-empty)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; Fin-UU-Fin-Level; UU-Fin; type-UU-Fin;
    Fin-UU-Fin)
```

## Idea

2-element types are types that are merely equivalent to the standard 2-element type `Fin 2`.

## Properties

### Characterization of the identity type of the type of 2-element types

```agda
ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → (Fin 2 ≃ X) → X
ev-zero-equiv-Fin-two-ℕ e = map-equiv e zero-Fin

inv-ev-zero-equiv-Fin-two-ℕ' :
  Fin 2 → (Fin 2 ≃ Fin 2)
inv-ev-zero-equiv-Fin-two-ℕ' (inl (inr star)) = id-equiv
inv-ev-zero-equiv-Fin-two-ℕ' (inr star) = equiv-succ-Fin

abstract
  issec-inv-ev-zero-equiv-Fin-two-ℕ' :
    (ev-zero-equiv-Fin-two-ℕ ∘ inv-ev-zero-equiv-Fin-two-ℕ') ~ id
  issec-inv-ev-zero-equiv-Fin-two-ℕ' (inl (inr star)) = refl
  issec-inv-ev-zero-equiv-Fin-two-ℕ' (inr star) = refl

  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    Id (map-equiv e zero-Fin) x →
    Id (map-equiv e one-Fin) y → htpy-equiv (inv-ev-zero-equiv-Fin-two-ℕ' x) e
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inr star) = inv q
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inr star) = inv q
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inr star) (inr star) p q (inl (inr star)) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
    (inr star) (inr star) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))

  isretr-inv-ev-zero-equiv-Fin-two-ℕ' :
    (inv-ev-zero-equiv-Fin-two-ℕ' ∘ ev-zero-equiv-Fin-two-ℕ) ~ id
  isretr-inv-ev-zero-equiv-Fin-two-ℕ' e =
    eq-htpy-equiv
      ( aux-isretr-inv-ev-zero-equiv-Fin-two-ℕ' e
        ( map-equiv e zero-Fin)
        ( map-equiv e one-Fin)
        ( refl)
        ( refl))

abstract
  is-equiv-ev-zero-equiv-Fin-two-ℕ' :
    is-equiv (ev-zero-equiv-Fin-two-ℕ {lzero} {Fin 2})
  is-equiv-ev-zero-equiv-Fin-two-ℕ' =
    is-equiv-has-inverse
      inv-ev-zero-equiv-Fin-two-ℕ'
      issec-inv-ev-zero-equiv-Fin-two-ℕ'
      isretr-inv-ev-zero-equiv-Fin-two-ℕ'

abstract
  is-equiv-ev-zero-equiv-Fin-two-ℕ :
    {l1 : Level} {X : UU l1} → mere-equiv (Fin 2) X →
    is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {X})
  is-equiv-ev-zero-equiv-Fin-two-ℕ {l1} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-equiv-Prop (ev-zero-equiv-Fin-two-ℕ))
      ( λ α →
        is-equiv-left-factor'
          ( ev-zero-equiv-Fin-two-ℕ)
          ( map-equiv (equiv-postcomp-equiv α (Fin 2)))
          ( is-equiv-comp
            ( ( ev-zero-equiv-Fin-two-ℕ) ∘
              ( map-equiv (equiv-postcomp-equiv α (Fin 2))))
            ( map-equiv α)
            ( ev-zero-equiv-Fin-two-ℕ)
            ( refl-htpy)
            ( is-equiv-ev-zero-equiv-Fin-two-ℕ')
            ( is-equiv-map-equiv α))
          ( is-equiv-comp-equiv α (Fin 2)))

equiv-ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → mere-equiv (Fin 2) X → (Fin 2 ≃ X) ≃ X
pr1 (equiv-ev-zero-equiv-Fin-two-ℕ e) = ev-zero-equiv-Fin-two-ℕ
pr2 (equiv-ev-zero-equiv-Fin-two-ℕ e) = is-equiv-ev-zero-equiv-Fin-two-ℕ e

abstract
  is-contr-total-UU-Fin-Level-two-ℕ :
    {l : Level} → is-contr (Σ (UU-Fin-Level l 2) type-UU-Fin-Level)
  is-contr-total-UU-Fin-Level-two-ℕ {l} =
    is-contr-equiv'
      ( Σ ( UU-Fin-Level l 2)
          ( λ X → raise-Fin l 2 ≃ type-UU-Fin-Level X))
      ( equiv-tot
        ( λ X →
          ( equiv-ev-zero-equiv-Fin-two-ℕ (pr2 X)) ∘e
          ( equiv-precomp-equiv (equiv-raise-Fin l 2) (pr1 X))))
      ( is-contr-total-equiv-subuniverse
        ( mere-equiv-Prop (Fin 2))
        ( Fin-UU-Fin-Level l 2))

abstract
  is-contr-total-UU-Fin-two-ℕ :
    is-contr (Σ (UU-Fin 2) (λ X → type-UU-Fin X))
  is-contr-total-UU-Fin-two-ℕ = is-contr-total-UU-Fin-Level-two-ℕ

point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  Id (Fin-UU-Fin-Level l 2) X → type-UU-Fin-Level X
point-eq-UU-Fin-Level-two-ℕ refl = map-raise zero-Fin

abstract
  is-equiv-point-eq-UU-Fin-Level-two-ℕ :
    {l : Level} (X : UU-Fin-Level l 2) →
    is-equiv (point-eq-UU-Fin-Level-two-ℕ {l} {X})
  is-equiv-point-eq-UU-Fin-Level-two-ℕ {l} =
    fundamental-theorem-id
      ( Fin-UU-Fin-Level l 2)
      ( map-raise zero-Fin)
      ( is-contr-total-UU-Fin-Level-two-ℕ)
      ( λ X → point-eq-UU-Fin-Level-two-ℕ {l} {X})

equiv-point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  Id (Fin-UU-Fin-Level l 2) X ≃ type-UU-Fin-Level X
pr1 (equiv-point-eq-UU-Fin-Level-two-ℕ {l} {X}) =
  point-eq-UU-Fin-Level-two-ℕ
pr2 (equiv-point-eq-UU-Fin-Level-two-ℕ {l} {X}) =
  is-equiv-point-eq-UU-Fin-Level-two-ℕ X

eq-point-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  type-UU-Fin-Level X → Id (Fin-UU-Fin-Level l 2) X
eq-point-UU-Fin-Level-two-ℕ =
  map-inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ

point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → Id (Fin-UU-Fin 2) X → type-UU-Fin X
point-eq-UU-Fin-two-ℕ refl = zero-Fin

abstract
  is-equiv-point-eq-UU-Fin-two-ℕ :
    (X : UU-Fin 2) → is-equiv (point-eq-UU-Fin-two-ℕ {X})
  is-equiv-point-eq-UU-Fin-two-ℕ =
    fundamental-theorem-id
      ( Fin-UU-Fin 2)
      ( zero-Fin)
      ( is-contr-total-UU-Fin-two-ℕ)
      ( λ X → point-eq-UU-Fin-two-ℕ {X})

equiv-point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → Id (Fin-UU-Fin 2) X ≃ type-UU-Fin X
pr1 (equiv-point-eq-UU-Fin-two-ℕ {X}) = point-eq-UU-Fin-two-ℕ
pr2 (equiv-point-eq-UU-Fin-two-ℕ {X}) = is-equiv-point-eq-UU-Fin-two-ℕ X

eq-point-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → type-UU-Fin X → Id (Fin-UU-Fin 2) X
eq-point-UU-Fin-two-ℕ {X} =
  map-inv-equiv equiv-point-eq-UU-Fin-two-ℕ

-- Corollary 17.4.2

abstract
  no-section-type-UU-Fin-Level-two-ℕ :
    {l : Level} → ¬ ((X : UU-Fin-Level l 2) → type-UU-Fin-Level X)
  no-section-type-UU-Fin-Level-two-ℕ {l} f =
    is-not-contractible-Fin 2
      ( Eq-eq-ℕ)
      ( is-contr-equiv
        ( Id (Fin-UU-Fin-Level l 2) (Fin-UU-Fin-Level l 2))
        ( ( inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ) ∘e
          ( equiv-raise-Fin l 2))
        ( is-prop-is-contr
          ( pair
            ( Fin-UU-Fin-Level l 2)
            ( λ X → eq-point-UU-Fin-Level-two-ℕ (f X)))
          ( Fin-UU-Fin-Level l 2)
          ( Fin-UU-Fin-Level l 2)))

abstract
  no-section-type-UU-Fin-two-ℕ :
    ¬ ((X : UU-Fin 2) → type-UU-Fin X)
  no-section-type-UU-Fin-two-ℕ f =
    no-section-type-UU-Fin-Level-two-ℕ f
```

```agda
abstract
  is-not-decidable-type-UU-Fin-Level-two-ℕ :
    {l : Level} →
    ¬ ((X : UU-Fin-Level l 2) → is-decidable (type-UU-Fin-Level X))
  is-not-decidable-type-UU-Fin-Level-two-ℕ {l} d =
    no-section-type-UU-Fin-Level-two-ℕ
      ( λ X →
        map-right-unit-law-coprod-is-empty
          ( pr1 X)
          ( ¬ (pr1 X))
          ( apply-universal-property-trunc-Prop
            ( pr2 X)
            ( dn-Prop' (pr1 X))
            ( λ e → intro-dn {l} (map-equiv e zero-Fin)))
          ( d X))
```
