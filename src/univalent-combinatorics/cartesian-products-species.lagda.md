# Cartesian product of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-products-species where


open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.exponents-species
```

# Idea

We caracterize the type cartesian product of species as the castesian product of species on objects.

## Definition

```agda 
species-cartesian-prod :
  {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
species-cartesian-prod F G X = (F X) × (G X)

-- species-cartesian-prod' :
--  {l1 l2 : Level} (F : species l1) (G : species l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
-- species-cartesian-prod' F G = (X : 𝔽) → (F X) × (G X)

_×ˢ_,_ :  {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
F ×ˢ G , X = species-cartesian-prod F G X 
``` 

## Universal properties

Proof of ((species-cartesian-prod F G) →ˢ H) ≃ ( F →ˢ exponents-species G H).


```agda 
equiv-universal-property-exponents-species :
  {l1 l2 l3 : Level} (F : species l1) (G : species l2) (H : species l3) →
  ((species-cartesian-prod F G) →ˢ H) ≃
  ( F →ˢ exponents-species G H)
equiv-universal-property-exponents-species F G H =
  equiv-map-Π (λ X → equiv-ev-pair)
  
``` 
