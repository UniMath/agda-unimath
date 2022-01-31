# The universal property of dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-dependent-pair-types where

open import foundation.dependent-pair-types using
  ( Σ; pair; pr1; pr2; ev-pair; ind-Σ)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using (refl)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of dependent pair types gives us a characterization of maps out of a dependent pair types.

## Theorem

```agda
abstract
  is-equiv-ev-pair :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
    is-equiv (ev-pair {C = C})
  pr1 (pr1 is-equiv-ev-pair) = ind-Σ
  pr2 (pr1 is-equiv-ev-pair) = refl-htpy
  pr1 (pr2 is-equiv-ev-pair) = ind-Σ
  pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (pair a b))
pr1 equiv-ev-pair = ev-pair
pr2 equiv-ev-pair = is-equiv-ev-pair
```
