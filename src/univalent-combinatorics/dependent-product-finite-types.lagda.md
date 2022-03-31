---
title: Dependent products of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.dependent-product-finite-types where

open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting-dependent-function-types using
  ( count-Π)
open import univalent-combinatorics.finite-choice using (finite-choice)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; 𝔽; type-𝔽; is-finite-type-𝔽)
```

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
