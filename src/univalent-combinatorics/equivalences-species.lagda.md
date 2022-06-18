# Equivalences of species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equivalences-species where

open import foundation.functions using (id; _∘_)

open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import foundation.identity-types using
    (Id; tr; inv; concat; refl; ap; eq-transpose-tr; eq-transpose-tr'; inv-inv; _∙_)

open import foundation.univalence using (univalence; equiv-eq; eq-equiv; eq-equiv-fam; equiv-eq-fam; is-equiv-equiv-eq-fam)

open import foundation.equivalences using (_≃_; map-equiv)

open import  foundation.dependent-pair-types using (pair; Σ; pr1; pr2)

open import foundation.equality-dependent-function-types using (is-contr-total-Eq-Π)

open import foundation.contractible-types using (is-contr)

open import univalent-combinatorics.finite-types using (𝔽)

open import univalent-combinatorics.species

```

## Idea

In this file, we define the type of species equivalences
and prove the univalence principle for species. An equivalence
of species is a pointwise family of equivalences between their
values.

### Definition

```agda
eqiv-species : {l1 l2 : Level} → species l1 → species l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
eqiv-species F G = (X : 𝔽) → F X ≃ G X 
```

### The identity type of species is equivalent to the type of equivalences between them

```agda
species-is-equiv-Id : {l : Level} → (F G : species l) → (Id F G) ≃ (eqiv-species F G)  
pr1 (species-is-equiv-Id F G) = equiv-eq-fam F G
pr2 (species-is-equiv-Id F G) = is-equiv-equiv-eq-fam F G
```

 