# Cartesian product of finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-product-finite-types where

open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-cartesian-product-types using (equiv-prod)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting using (count)
open import univalent-combinatorics.counting-cartesian-product-types using
  ( count-prod; count-left-factor; count-right-factor)
open import univalent-combinatorics.equivalences-standard-finite-types using
  ( prod-Fin)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; is-finite-count; 𝔽; type-𝔽; is-finite-type-𝔽;
    UU-Fin-Level; UU-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

The cartesian product of finite types is finite. We obtain a cartesian product operation on finite types.

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
    functor-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    functor-trunc-Prop (λ e → count-right-factor e x) f

prod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (mul-ℕ k l)
pr1 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = X × Y
pr2 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-prod e1 e2 ∘e inv-equiv (prod-Fin k l))))

prod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (mul-ℕ k l)
prod-UU-Fin = prod-UU-Fin-Level
```
