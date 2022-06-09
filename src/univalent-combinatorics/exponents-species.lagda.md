# Exponents of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.exponents-species where

open import foundation-core.universe-levels using (Level; UU; _⊔_)
open import foundation-core.cartesian-product-types using (_×_; prod)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)

open import foundation.universe-levels using (Level; UU; lsuc; lzero)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.equivalences using (_≃_; map-equiv)
open import foundation.functoriality-coproduct-types 

open import univalent-combinatorics.finite-types using (𝔽; type-𝔽)
open import univalent-combinatorics.species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species




```
# Idea

We caracterize the type exponents of species on objects as a map from F X → G X for given species F, G and object X.

## Definition
### exponents of species on objects


```agda 
exponents-species : {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
exponents-species F G X  = F X → G X

_⇒ˢ_,_ : {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
F ⇒ˢ G , X = exponents-species F G X
  
```
