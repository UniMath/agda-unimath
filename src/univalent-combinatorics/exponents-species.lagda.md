# Exponents of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.exponents-species where

open import univalent-combinatorics.species

open import foundation.coproduct-types using (coprod; inl; inr)

open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.universe-levels using (Level; UU; lsuc; lzero)

open import univalent-combinatorics.finite-types using (𝔽)

open import foundation.equivalences using (_≃_; map-equiv)

open import foundation-core.cartesian-product-types using (_×_; prod)

open import univalent-combinatorics.finite-types

open import univalent-combinatorics.morphisms-species

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)

open import foundation.functoriality-coproduct-types 
```
# Idea

## Definition
### exponents of species on objects


```agda 
_⇒ˢ_,_ : {l1 l2 : Level} → species l1 → species l2 → 𝔽 → UU (l1 ⊔ l2)
F ⇒ˢ G , X = F X → G X
--_⇒ˢ_,_  F G X = (Y : 𝔽) → prod (X ≃ Y) (F Y) → G Y
```

```agda 
--_⇒ˢ'_,_ : {l1 l2 : Level} → species l1 → species l2 → ? → {!   !}
--_⇒ˢ'_,_ F G X = (Y : ?) → (X ≃ Y) (F Y) → G Y
```  