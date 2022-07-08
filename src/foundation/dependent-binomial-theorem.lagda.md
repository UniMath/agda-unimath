---
title: The dependent binomial theorem for types (Distributivity of dependent function types over coproduct types)
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.dependent-binomial-theorem where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (equiv-diagonal-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (ap; equiv-tr)
open import foundation.raising-universe-levels using
  ( raise; map-inv-raise; map-raise; isretr-map-inv-raise; issec-map-inv-raise;
    equiv-raise)
open import foundation.type-theoretic-principle-of-choice using
  ( distributive-Π-Σ)
open import foundation.unit-type using (star)
open import foundation.universal-property-coproduct-types using
  ( equiv-universal-property-coprod)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.equality-standard-finite-types using
  ( is-contr-is-zero-or-one-Fin-two-ℕ)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; is-zero-Fin; is-one-Fin)
```

## Idea

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  fam-coprod :
    Fin 2  → UU (l1 ⊔ l2)
  fam-coprod (inl (inr star)) = raise l2 A
  fam-coprod (inr star) = raise l1 B
  
  map-compute-total-fam-coprod :
    Σ (Fin 2) fam-coprod → coprod A B
  map-compute-total-fam-coprod (pair (inl (inr star)) y) = inl (map-inv-raise y)
  map-compute-total-fam-coprod (pair (inr star) y) = inr (map-inv-raise y)

  map-inv-compute-total-fam-coprod :
    coprod A B → Σ (Fin 2) fam-coprod
  pr1 (map-inv-compute-total-fam-coprod (inl x)) = zero-Fin 1
  pr2 (map-inv-compute-total-fam-coprod (inl x)) = map-raise x
  pr1 (map-inv-compute-total-fam-coprod (inr x)) = one-Fin 1
  pr2 (map-inv-compute-total-fam-coprod (inr x)) = map-raise x

  issec-map-inv-compute-total-fam-coprod :
    (map-compute-total-fam-coprod ∘ map-inv-compute-total-fam-coprod) ~ id
  issec-map-inv-compute-total-fam-coprod (inl x) =
    ap inl (isretr-map-inv-raise {l2} x)
  issec-map-inv-compute-total-fam-coprod (inr x) =
    ap inr (isretr-map-inv-raise {l1} x)

  isretr-map-inv-compute-total-fam-coprod :
    (map-inv-compute-total-fam-coprod ∘ map-compute-total-fam-coprod) ~ id
  isretr-map-inv-compute-total-fam-coprod (pair (inl (inr star)) y) =
    ap (pair (zero-Fin 1)) (issec-map-inv-raise y)
  isretr-map-inv-compute-total-fam-coprod (pair (inr star) y) =
    ap (pair (one-Fin 1)) (issec-map-inv-raise y)

  is-equiv-map-compute-total-fam-coprod :
    is-equiv map-compute-total-fam-coprod
  is-equiv-map-compute-total-fam-coprod =
    is-equiv-has-inverse
      map-inv-compute-total-fam-coprod
      issec-map-inv-compute-total-fam-coprod
      isretr-map-inv-compute-total-fam-coprod
  
  compute-total-fam-coprod :
    (Σ (Fin 2) fam-coprod) ≃ coprod A B
  pr1 compute-total-fam-coprod = map-compute-total-fam-coprod
  pr2 compute-total-fam-coprod = is-equiv-map-compute-total-fam-coprod

  inv-compute-total-fam-coprod :
    coprod A B ≃ Σ (Fin 2) fam-coprod
  inv-compute-total-fam-coprod =
    inv-equiv compute-total-fam-coprod
  
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  type-distributive-Π-coprod : UU (l1 ⊔ l2 ⊔ l3)
  type-distributive-Π-coprod =
    Σ ( X → Fin 2)
      ( λ f → ((x : X) (p : is-zero-Fin 2 (f x)) → A x) ×
              ((x : X) (p : is-one-Fin 2 (f x)) → B x))

  distributive-Π-coprod :
    ((x : X) → coprod (A x) (B x)) ≃ type-distributive-Π-coprod
  distributive-Π-coprod =
    ( ( equiv-tot
        ( λ f →
          ( ( equiv-prod
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (equiv-raise l3 (A x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (equiv-raise l2 (B x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))) ∘e
            ( distributive-Π-Σ)) ∘e
          ( equiv-map-Π
            ( λ x →
              ( equiv-universal-property-coprod
                ( fam-coprod (A x) (B x) (f x))) ∘e
              ( equiv-diagonal-is-contr
                ( fam-coprod (A x) (B x) (f x))
                ( is-contr-is-zero-or-one-Fin-two-ℕ (f x))))))) ∘e
      ( distributive-Π-Σ)) ∘e
    ( equiv-map-Π
      ( λ x → inv-compute-total-fam-coprod (A x) (B x)))
```
  
