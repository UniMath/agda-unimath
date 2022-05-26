# Morphisms of finite species

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.morphisms-finite-species where

open import foundation-core.sets using (UU-Set; is-set)

open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-is-equiv;
    is-prop-Π)

open import foundation.identity-types using
    (Id; tr; inv; concat; refl; ap; eq-transpose-tr; eq-transpose-tr'; inv-inv; _∙_)

open import foundation.contractible-types using (is-contr)

open import foundation.univalence using (eq-equiv)

open import foundation.equivalences using (is-equiv; map-inv-is-equiv)

open import foundation.dependent-pair-types using (pair; Σ; pr1; pr2)

open import foundation.fundamental-theorem-of-identity-types using (fundamental-theorem-id)

open import foundation.equality-dependent-function-types using (is-contr-total-Eq-Π)

open import foundation.homotopies using (_~_; is-contr-total-htpy)

open import univalent-combinatorics.finite-types using (𝔽)

open import foundation.functions using (_∘_)

open import univalent-combinatorics.finite-species

```

# Idea

A morphism between two finite species is a pointwise family of maps between the species' values.

## Definition

```agda
_→ˢ'_ : finite-species → finite-species → {!   !}
_→ˢ'_ F G = {! (X : 𝔽) → F X → G X  !}
```