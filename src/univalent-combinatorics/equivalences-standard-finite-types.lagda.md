# Equivalences between standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equivalences-standard-finite-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.exponentiation-natural-numbers using
  ( exp-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (equiv-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (pair; pr1; pr2; Σ)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using
  ( eq-htpy-equiv; htpy-equiv; htpy-eq-equiv; _≃_; id-equiv; is-equiv-has-inverse;
    _∘e_; inv-equiv; map-inv-equiv; map-equiv)
open import foundation.equivalences-maybe using (equiv-equiv-Maybe)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.functoriality-coproduct-types using
  ( compose-map-coprod; equiv-coprod; retr-equiv-coprod)
open import foundation.identity-types using (Id; inv; refl; ap; _∙_)
open import foundation.type-arithmetic-coproduct-types using
  ( inv-assoc-coprod; right-distributive-prod-coprod)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod; left-absorption-prod; inv-left-unit-law-coprod)
open import foundation.type-arithmetic-unit-type using (left-unit-law-prod)
open import foundation.unit-type using (unit; is-contr-unit; star)
open import foundation.universal-property-coproduct-types using
  ( equiv-universal-property-coprod)
open import foundation.universal-property-empty-type using
  ( universal-property-empty')
open import foundation.universal-property-unit-type using
  ( equiv-universal-property-unit)

open import foundation-core.equality-dependent-pair-types using
  ( eq-pair-Σ; pair-eq-Σ)
open import foundation-core.functions using (id)
open import foundation-core.homotopies using (refl-htpy)
open import foundation-core.propositions using (eq-is-prop)
open import foundation-core.sets using (Id-Prop)

open import univalent-combinatorics.standard-finite-types using (Fin; zero-Fin)
open import univalent-combinatorics.equality-standard-finite-types using (Fin-Set)
```

## Idea

We construct equivalences between (types built out of) standard finite types.

### Fin is injective

```agda
abstract
  is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
  is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
  is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
    ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))
```

### The standard finite types are closed under coproducts

```agda
coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) id-equiv) ∘e inv-assoc-coprod

Fin-add-ℕ :
  (k l : ℕ) → Fin (add-ℕ k l) ≃ coprod (Fin k) (Fin l)
Fin-add-ℕ k l = inv-equiv (coprod-Fin k l)
```

### The standard finite types are closed under cartesian products

```
prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) left-unit-law-prod)) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (mul-ℕ k l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (prod-Fin k l)
```

### The standard finite types are closed under function types

```agda
function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coprod unit) ∘e
  ( equiv-is-contr (universal-property-empty' (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( ( prod-Fin (exp-ℕ l k) l) ∘e
    ( equiv-prod (function-Fin k l) (equiv-universal-property-unit (Fin l)))) ∘e
  ( equiv-universal-property-coprod (Fin l))

Fin-exp-ℕ : (k l : ℕ) → Fin (exp-ℕ l k) ≃ (Fin k → Fin l)
Fin-exp-ℕ k l = inv-equiv (function-Fin k l)
```

### The type of automorphisms on `Fin n` is equivalent to the type of automorphisms on `Fin (succ-ℕ n)` that fix `inr star`

```agda
extend-permutation-Fin-n : (n : ℕ) →
  (Fin n ≃ Fin n) ≃ (Σ (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) (λ e → Id (map-equiv e (inr star)) (inr star)))
pr1 (pr1 (extend-permutation-Fin-n n) f) = equiv-coprod f id-equiv
pr2 (pr1 (extend-permutation-Fin-n n) f) = refl
pr2 (extend-permutation-Fin-n n) =
  is-equiv-has-inverse
    ( λ f → pr1 (retr-equiv-coprod (pr1 f) id-equiv (p f)))
    ( λ f →
      ( eq-pair-Σ
        ( inv (eq-htpy-equiv (pr2 (retr-equiv-coprod (pr1 f) id-equiv (p f)))))
        ( eq-is-prop (pr2 (Id-Prop (Fin-Set (succ-ℕ n)) (map-equiv (pr1 f) (inr star)) (inr star))))))
    ( λ f → eq-htpy-equiv refl-htpy)
  where
  p : (f : (Σ (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) (λ e → Id (map-equiv e (inr star)) (inr star))))
    (b : unit) → Id (map-equiv (pr1 f) (inr b)) (inr b) 
  p f star = pr2 f

computation-extend-permutation-Fin-n : (n : ℕ) → (f : Fin n ≃ Fin n) → (x y : Fin n) →
  Id (map-equiv f x) y → Id (map-equiv (pr1 (map-equiv (extend-permutation-Fin-n n) f)) (inl x)) (inl y)
computation-extend-permutation-Fin-n n f x y p = ap inl p

computation-inv-extend-permutation-Fin-n : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
  (p : Id (map-equiv f (inr star)) (inr star)) → (x : Fin n) →
  Id (inl (map-equiv (map-inv-equiv (extend-permutation-Fin-n n) (pair f p)) x)) (map-equiv f (inl x))
computation-inv-extend-permutation-Fin-n n f p x =
  htpy-eq-equiv (pr1 (pair-eq-Σ (pr2 (pr1 (pr2 (extend-permutation-Fin-n n))) (pair f p)))) (inl x)

comp-extend-permutation-Fin-n : (n : ℕ) (f g : Fin n ≃ Fin n) →
  htpy-equiv
    ( pr1 (map-equiv (extend-permutation-Fin-n n) (f ∘e g)))
    ( (pr1 (map-equiv (extend-permutation-Fin-n n) f)) ∘e (pr1 (map-equiv (extend-permutation-Fin-n n) g)))
comp-extend-permutation-Fin-n n f g = compose-map-coprod (map-equiv g) (map-equiv f) id id
```
