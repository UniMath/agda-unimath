# The univalence axiom implies function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.univalence-implies-function-extensionality where

open import foundation-core.contractible-maps using (is-contr-map-is-equiv)
open import foundation-core.contractible-types using (is-contr-retract-of)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; is-equiv; map-equiv; is-equiv-id)
open import foundation-core.fibers-of-maps using (fib)
open import foundation-core.functions using (postcomp; id)
open import foundation-core.homotopies using (refl-htpy)
open import foundation-core.identity-types using (refl; tr)
open import foundation-core.type-arithmetic-dependent-pair-types using
  ( equiv-pr1)
open import foundation-core.universe-levels using (Level; UU)

open import foundation.equivalence-induction using (ind-equiv)
open import foundation.function-extensionality using (htpy-eq; FUNEXT)
open import foundation.weak-function-extensionality using
  ( WEAK-FUNEXT; FUNEXT-WEAK-FUNEXT)

```

## Idea

The univalence axiom implies function extensionality

## Theorem

```agda
abstract
  is-equiv-postcomp-univalence :
    {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
    is-equiv (postcomp A (map-equiv e))
  is-equiv-postcomp-univalence {X = X} A =
    ind-equiv X (λ Y e → is-equiv (postcomp A (map-equiv e))) is-equiv-id

-- Theorem 17.2.2

abstract
  weak-funext-univalence :
    {l : Level} {A : UU l} {B : A → UU l} → WEAK-FUNEXT A B
  weak-funext-univalence {A = A} {B} is-contr-B =
    is-contr-retract-of
      ( fib (postcomp A (pr1 {B = B})) id)
      ( pair
        ( λ f → pair (λ x → pair x (f x)) refl)
        ( pair
          ( λ h x → tr B (htpy-eq (pr2 h) x) (pr2 (pr1 h x)))
          ( refl-htpy)))
      ( is-contr-map-is-equiv
        ( is-equiv-postcomp-univalence A (equiv-pr1 is-contr-B))
        ( id))

abstract
  funext-univalence :
    {l : Level} {A : UU l} {B : A → UU l} (f : (x : A) → B x) → FUNEXT f
  funext-univalence {A = A} {B} f =
    FUNEXT-WEAK-FUNEXT (λ A B → weak-funext-univalence) A B f
```
