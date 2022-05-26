# Coproduct of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.coproducts-species where

open import univalent-combinatorics.species

open import foundation.coproduct-types using (coprod; inl; inr)

open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.universe-levels using (Level; UU; lsuc; lzero)

open import univalent-combinatorics.finite-types using (𝔽)

open import univalent-combinatorics.morphisms-species

open import foundation.functoriality-coproduct-types 
```



# Idea


## Definition
### coproduct on objects

```agda
species-coprod :  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
species-coprod F G X = coprod (F X) (G X)

_+ˢ_,_ : {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
F +ˢ G , X = species-coprod F G X
```

### coproduct on morphisms
```agda
--species-coprod-morphisms :  {l1 l2 : Level} {X Y : 𝔽} (F : species l1) (G : species l2) (σ :  X → Y) → {!   !}
--species-coprod-morphisms F G σ  = map-coprod (F σ) (G σ) {! !}
```


   