# Cartesian product of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-products-species where

open import univalent-combinatorics.species

open import foundation-core.cartesian-product-types using (_×_)

open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.finite-types using (𝔽)
```

# Idea


## Definition

```agda 
species-prod :  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
species-prod F G X = (F X) × (G X)

_×ˢ_,_ :  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
F ×ˢ G , X = species-prod F G X 
``` 
