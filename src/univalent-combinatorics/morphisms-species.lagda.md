# Morphisms of species

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.morphisms-species where

open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import foundation.identity-types using (Id; refl)

open import foundation.contractible-types using (is-contr)

open import foundation.equivalences using (is-equiv; map-inv-is-equiv)

open import foundation.dependent-pair-types using (Σ)

open import foundation.fundamental-theorem-of-identity-types using (fundamental-theorem-id)

open import foundation.equality-dependent-function-types using (is-contr-total-Eq-Π)

open import foundation.homotopies using (_~_; is-contr-total-htpy)

open import univalent-combinatorics.finite-types using (𝔽)

open import univalent-combinatorics.equality-finite-types using
  ( is-set-is-finite )

open import univalent-combinatorics.species
```

### Idea

A homomorphism between two species is a pointwise family of
maps between their values.

## Definition

```agda
hom-species : {l1 l2 : Level} → species l1 → species l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
hom-species F G = (X : 𝔽) → F X → G X
```

### We characterise the identity type of species morphisms as
homotopies.

```agda
htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (hom-species F G) → (hom-species F G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
htpy-hom-species {F = F} f g       = (X : 𝔽) → (y : F X) → Id (f X y) (g X y)

refl-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : hom-species F G) → (htpy-hom-species f f)
refl-htpy-hom-species f X y = refl 

is-contr-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2}
  → (f : hom-species F G) → is-contr (Σ (hom-species F G) (λ g → htpy-hom-species f g) )
is-contr-htpy-hom-species f = is-contr-total-Eq-Π (λ X h → f X ~ h) (λ X → is-contr-total-htpy (f X) )

htpy-eq-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → {f g : hom-species F G} → Id f g → htpy-hom-species f g
htpy-eq-hom-species refl X y = refl

is-equiv-htpy-eq-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2}
  → (f g : hom-species F G) → is-equiv (htpy-eq-hom-species {f = f} {g = g})
is-equiv-htpy-eq-hom-species f =
  fundamental-theorem-id f (refl-htpy-hom-species f) (is-contr-htpy-hom-species f) (λ g → htpy-eq-hom-species {f = f} {g = g})

eq-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → {f g : hom-species F G} → htpy-hom-species f g → Id f g 
eq-htpy-hom-species {f = f} {g = g} = map-inv-is-equiv (is-equiv-htpy-eq-hom-species f g)
```

### The identity homomorphism of species

```agda
id-hom-species : {l : Level} → (F : species l) → hom-species F F
id-hom-species F = λ X x → x 
```

### Composition of morphisms of species

```agda
comp-hom-species : {l1 l2 l3 : Level} → {F : species l1} → {G : species l2} → {H : species l3}
                                             → (hom-species G H) → (hom-species F G) → (hom-species F H)
comp-hom-species f g = λ X x → f X (g X x)
```

## Associativity of composition of homomorphisms of species

```agda
associative-law-comp-hom-species : {l1 l2 l3 l4 : Level}
                    → {F : species l1} → {G : species l2} → {H : species l3} → {I : species l4}
                    → (f : hom-species F G) → (g : hom-species G H) → (h : hom-species H I)
                    → Id (comp-hom-species h (comp-hom-species g f)) (comp-hom-species (comp-hom-species h g) f)
associative-law-comp-hom-species f g h = eq-htpy-hom-species (λ X y → refl)
```
## The left and right unit laws for composition of homomorphisms of species

```agda
left-unit-law-comp-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : hom-species F G)
                                                      → Id (comp-hom-species (id-hom-species G) f) f
left-unit-law-comp-hom-species f = eq-htpy-hom-species (λ X y → refl)

right-unit-law-comp-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : hom-species F G)
                                                      → Id (comp-hom-species f (id-hom-species F)) f
right-unit-law-comp-hom-species f = eq-htpy-hom-species (λ X y → refl)
```
