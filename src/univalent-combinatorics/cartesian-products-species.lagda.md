# Cartesian product of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-products-species where

open import univalent-combinatorics.species

open import foundation-core.cartesian-product-types using (_×_)

open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.universe-levels using (Level; UU; lsuc; lzero)

open import univalent-combinatorics.finite-types using (𝔽)

open import univalent-combinatorics.morphisms-species
```

# Idea


## Definition

```agda 
species-cartesian-prod :  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
species-cartesian-prod F G X = (F X) × (G X)

species-cartesian-prod' :  {l1 l2 : Level} (F : species l1) (G : species l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
species-cartesian-prod' F G = (X : 𝔽) → (F X) × (G X)

_×ˢ_,_ :  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
F ×ˢ G , X = species-cartesian-prod F G X 

universal-property-exponents-species : {l1 l2 l3 : Level} (F : species l1)(G : species l2)(H : species l3) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-exponents-species F G H = (X : 𝔽) → (species-cartesian-prod F G X) → H X
``` 
