---
title: Coproducts of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.coproduct-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using
  ( coprod; inl; inr; equiv-left-summand; equiv-right-summand; is-left-Prop;
    is-right-Prop)
open import foundation.decidable-subtypes using
  ( is-left-decidable-Prop; is-right-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv; _≃_; id-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.identity-types using (Id; refl; _∙_; inv)
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.type-arithmetic-coproduct-types using
  ( inv-assoc-coprod)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; count-equiv)
open import univalent-combinatorics.counting-decidable-subtypes using
  ( count-decidable-subtype)
open import univalent-combinatorics.double-counting using (double-counting)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; is-finite-count; 𝔽; type-𝔽; is-finite-type-𝔽;
    UU-Fin-Level; UU-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Coproducts of finite types are finite, giving a coproduct operation on the type 𝔽 of finite types.

## Properties

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

### Types equipped with a count are closed under coproducts

```agda
count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
pr1 (count-coprod (pair k e) (pair l f)) = add-ℕ k l
pr2 (count-coprod (pair k e) (pair l f)) =
  (equiv-coprod e f) ∘e (inv-equiv (coprod-Fin k l))

abstract
  number-of-elements-count-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coprod e f))
      ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
  number-of-elements-count-coprod (pair k e) (pair l f) = refl
```

### If `X + Y` has a count, then both `X` and `Y` have a count

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where
  
  count-left-summand : count (coprod X Y) → count X
  count-left-summand e =
    count-equiv
      ( equiv-left-summand)
      ( count-decidable-subtype is-left-decidable-Prop e)

  count-right-summand : count (coprod X Y) → count Y
  count-right-summand e =
    count-equiv
      ( equiv-right-summand)
      ( count-decidable-subtype is-right-decidable-Prop e)
```

### If each of `A`, `B`, and `A + B` come equipped with countings, then the number of elements of `A` and of `B` add up to the number of elements of `A + B`

```agda
abstract
  double-counting-coprod :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
    Id ( number-of-elements-count count-C)
       ( add-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  double-counting-coprod count-A count-B count-C =
    ( double-counting count-C (count-coprod count-A count-B)) ∙
    ( number-of-elements-count-coprod count-A count-B)

abstract
  sum-number-of-elements-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
    Id ( add-ℕ ( number-of-elements-count (count-left-summand e))
               ( number-of-elements-count (count-right-summand e)))
       ( number-of-elements-count e)
  sum-number-of-elements-coprod e =
    ( inv
      ( number-of-elements-count-coprod
        ( count-left-summand e)
        ( count-right-summand e))) ∙
    ( inv
      ( double-counting-coprod
        ( count-left-summand e)
        ( count-right-summand e) e))
```

### Finite types are closed under coproducts

```agda
abstract
  is-finite-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (coprod X Y)
  is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (coprod X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (coprod X Y))
          ( is-finite-count ∘ (count-coprod e)))

coprod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (coprod-𝔽 X Y) = coprod (type-𝔽 X) (type-𝔽 Y)
pr2 (coprod-𝔽 X Y) = is-finite-coprod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite X
  is-finite-left-summand =
    functor-trunc-Prop count-left-summand

abstract
  is-finite-right-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite Y
  is-finite-right-summand =
    functor-trunc-Prop count-right-summand

coprod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (add-ℕ k l)
pr1 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = coprod X Y
pr2 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coprod e1 e2 ∘e inv-equiv (coprod-Fin k l))))

coprod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (add-ℕ k l)
coprod-UU-Fin X Y = coprod-UU-Fin-Level X Y
```
