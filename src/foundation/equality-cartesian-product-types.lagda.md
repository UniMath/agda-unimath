---
title: Equality of cartesian product types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-cartesian-product-types where

open import foundation-core.equality-cartesian-product-types public

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types
open import foundation.universe-levels using (UU; Level; _⊔_)
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B} {p : a0 ＝ a1} {q : b0 ＝ b1}
  where

  expand-pair-outer : (eq-pair p q) ＝ ((eq-pair p refl) ∙ (eq-pair refl q))
  expand-pair-outer = ap (λ x → eq-pair x q) (inv right-unit) ∙ (eq-pair-concat p refl refl q)

  expand-pair-inner : (eq-pair p q) ＝ ((eq-pair refl q) ∙ (eq-pair p refl))
  expand-pair-inner = ( ap (λ x → eq-pair p x) (inv right-unit)) ∙ ( eq-pair-concat refl p q refl )
```
