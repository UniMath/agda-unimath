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

































```agda 
--_⇒ˢ'_,_ : {l1 l2 : Level} → species l1 → species l2 → ? → {!   !}
--_⇒ˢ'_,_ F G X = (Y : ?) → (X ≃ Y) (F Y) → G Y


-- _⇒ˢ_,_ : {l1 l2 : Level} → (F : species l1) → (G : species l2) → (X : 𝔽) → species (l1 ⊔ l2)
-- F ⇒ˢ G , X = type-𝔽 X → F X → G X
--_⇒ˢ_,_  F G X = (Y : 𝔽) → prod (X ≃ Y) (F Y) → G Y

-- exponents-species : {l1 l2 : Level} → species l1 → species l2 → 𝔽 → UU (l1 ⊔ l2)
-- exponents-species F G X = F ⇒ˢ G , X 

-- species-exponents-species : {l1 l2 : Level}{F : species l1}{G : species l2}(X : 𝔽) → (e : exponents-species F G X) → 𝔽 → (UU (lsuc (l1 ⊔ l2)))
-- species-exponents-species X e  =  ?

-- universal-property-exponents-species' : {l1 l2 l3 : Level} (F : species l1)(G : species l2)(H : species l3)→ {!   !}
-- universal-property-exponents-species' F G H = (X : 𝔽) → F →ˢ (exponents-species G H X)

```  