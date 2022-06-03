---
title: Counting the elements of dependent function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.dependent-function-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-function-types using
  ( equiv-precomp-Π)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.unit-type using (star)
open import foundation.universal-property-coproduct-types using
  ( equiv-dependent-universal-property-coprod)
open import foundation.universal-property-empty-type using
  ( dependent-universal-property-empty')
open import foundation.universal-property-unit-type using
  ( equiv-dependent-universal-property-unit)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.cartesian-product-types using
  ( count-prod)
open import univalent-combinatorics.counting using
  ( count; count-is-contr; count-equiv'; equiv-count; map-equiv-count)
open import univalent-combinatorics.finite-choice using (finite-choice)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; 𝔽; type-𝔽; is-finite-type-𝔽)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Dependent products of finite types indexed by a finite type are finite.

## Properties

### Counting dependent products indexed by standard finite types

If the elements of `A` can be counted and if for each `x : A` the elements of `B x` can be counted, then the elements of `Π A B` can be counted.

```agda
count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( e (inr star))))
```

### Counting on dependent function types

```agda
count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))
```

### Finiteness of dependent function types

```agda
abstract
  is-finite-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
  is-finite-Π {l1} {l2} {A} {B} f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop ((x : A) → B x))
      ( λ e →
        apply-universal-property-trunc-Prop
          ( finite-choice f g)
          ( is-finite-Prop ((x : A) → B x))
          ( λ h → unit-trunc-Prop (count-Π e h)))

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
pr1 (Π-𝔽 A B) = (x : type-𝔽 A) → type-𝔽 (B x)
pr2 (Π-𝔽 A B) = is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x))
```
