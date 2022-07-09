---
title: Cartesian products of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-product-types where

open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( equiv-is-contr; is-contr-total-path')
open import foundation.decidable-equality using
  ( has-decidable-equality-right-factor)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv; _≃_)
open import foundation.functions using (_∘_)
open import foundation.functoriality-cartesian-product-types using (equiv-prod)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation.type-arithmetic-coproduct-types using
  ( right-distributive-prod-coprod)
open import foundation.type-arithmetic-dependent-pair-types using
  ( assoc-Σ)
open import foundation.type-arithmetic-empty-type using
  ( left-absorption-prod)
open import foundation.type-arithmetic-unit-type using
  ( left-unit-law-prod; right-unit-law-prod)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.coproduct-types using (coprod-Fin)
open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; count-equiv; has-decidable-equality-count)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-Σ)
open import univalent-combinatorics.decidable-propositions using
  ( count-eq)
open import univalent-combinatorics.double-counting using (double-counting)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; is-finite-count; 𝔽; type-𝔽; is-finite-type-𝔽;
    UU-Fin-Level; UU-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

The cartesian product of finite types is finite. We obtain a cartesian product operation on finite types.

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

```agda
count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-prod (pair k e) (pair l f)) = mul-ℕ k l
pr2 (count-prod (pair k e) (pair l f)) =
  (equiv-prod e f) ∘e (inv-equiv (prod-Fin k l))

abstract
  number-of-elements-count-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    Id ( number-of-elements-count
         ( count-prod count-A count-B))
       ( mul-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x
```

```agda
abstract
  product-number-of-elements-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
    (a : A) (b : B) →
    Id ( mul-ℕ ( number-of-elements-count (count-left-factor count-AB b))
               ( number-of-elements-count (count-right-factor count-AB a)))
       ( number-of-elements-count count-AB)
  product-number-of-elements-prod count-AB a b =
    ( inv
      ( number-of-elements-count-prod
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))) ∙
    ( double-counting
      ( count-prod
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))
      ( count-AB))
```

```agda
abstract
  is-finite-prod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X × Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X × Y))
          ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (prod-𝔽 X Y) = (type-𝔽 X) × (type-𝔽 Y)
pr2 (prod-𝔽 X Y) = is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y =
    map-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    map-trunc-Prop (λ e → count-right-factor e x) f

prod-UU-Fin-Level :
  {l1 l2 : Level} (k l : ℕ) → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (mul-ℕ k l)
pr1 (prod-UU-Fin-Level k l (pair X H) (pair Y K)) = X × Y
pr2 (prod-UU-Fin-Level k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-prod e1 e2 ∘e inv-equiv (prod-Fin k l))))

prod-UU-Fin :
  (k l : ℕ) → UU-Fin k → UU-Fin l → UU-Fin (mul-ℕ k l)
prod-UU-Fin k l = prod-UU-Fin-Level k l
```
