# Coproduct of species

```agda
{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --allow-unsolved-metas #-}

module univalent-combinatorics.coproducts-species where



open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.distributivity-of-dependent-functions-over-dependent-pairs

open import univalent-combinatorics.species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.equivalences-species


 


```


# Idea
 
We caracterize the type coproduct of species as the coproduct of species on objects.

## Definition
### coproduct on objects

```agda


species-coprod :  {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
species-coprod F G X = coprod (F X) (G X)

_+ˢ_,_ : {l1 l2 : Level} → species l1 → species l2 → species (l1 ⊔ l2)
F +ˢ G , X = species-coprod F G X 
```

## Universal properties

Proof of (hom-species (species-coprod F G) H) ≃ ((hom-species F H) × (hom-species G H)).

```agda
equiv-universal-property-coproduct-species :
 {l1 l2 l3 : Level} (F : species l1) (G : species l2) (H : species l3) →
 (hom-species (species-coprod F G) H) ≃
 ((hom-species F H) × (hom-species G H))
equiv-universal-property-coproduct-species F G H =
  distributive-Π-Σ ∘e equiv-map-Π (λ X → ( (equiv-universal-property-coprod (H X)) ))
 
``` 



      