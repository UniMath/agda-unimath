# The coproduct operation on finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.coproduct-finite-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.mere-equivalences using (mere-equiv-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting using (count)
open import univalent-combinatorics.counting-coproduct-types using
  ( count-coprod; count-left-summand; count-right-summand)
open import univalent-combinatorics.equivalences-standard-finite-types using
  ( coprod-Fin)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; is-finite-count; 𝔽; type-𝔽; is-finite-type-𝔽;
    UU-Fin-Level; UU-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Coproducts of finite types are finite, giving a coproduct operation on the type 𝔽 of finite types.

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
