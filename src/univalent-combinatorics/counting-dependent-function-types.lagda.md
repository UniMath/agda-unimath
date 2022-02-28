# Counting the elements of dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-dependent-function-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.equivalences using (equiv-precomp-Π)
open import foundation.functions using (_∘_)
open import foundation.unit-type using (star)
open import foundation.universal-property-coproduct-types using
  ( equiv-dependent-universal-property-coprod)
open import foundation.universal-property-empty-type using
  ( dependent-universal-property-empty')
open import foundation.universal-property-unit-type using
  ( equiv-dependent-universal-property-unit)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting using
  ( count; count-is-contr; count-equiv'; equiv-count; map-equiv-count)
open import univalent-combinatorics.counting-cartesian-product-types using
  ( count-prod)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

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

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))
```
