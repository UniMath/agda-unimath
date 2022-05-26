# Morphisms of species

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.morphisms-species where

open import foundation-core.sets using (UU-Set; is-set)

open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-is-equiv;
    is-prop-Π)

open import foundation.identity-types using
    (Id; tr; inv; concat; refl; ap; eq-transpose-tr; eq-transpose-tr'; inv-inv; _∙_)

open import foundation.contractible-types using (is-contr)

open import foundation.univalence using (eq-equiv)

open import foundation.equivalences using (is-equiv; map-inv-is-equiv)

open import foundation.dependent-pair-types using (pair; Σ; pr1; pr2)

open import foundation.fundamental-theorem-of-identity-types using (fundamental-theorem-id)

open import foundation.equality-dependent-function-types using (is-contr-total-Eq-Π)

open import foundation.homotopies using (_~_; is-contr-total-htpy)

open import univalent-combinatorics.finite-types using (𝔽)

open import foundation.functions using (_∘_)

open import univalent-combinatorics.species

```

# Idea

A morphism between two species is a pointwise family of maps between the species' values.

## Definition

```agda
_→ˢ_ : {l1 l2 : Level} → species l1 → species l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
_→ˢ_ F G = (X : 𝔽) → F X → G X 
```

### We characterise the identity type of species morphisms

```agda
_∼ˢ_ : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (F →ˢ G) → (F →ˢ G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
_∼ˢ_ {F = F} f g       = (X : 𝔽) → (y : F X ) → Id (f X y) (g X y)

refl-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : F →ˢ G) → (f ∼ˢ f)
refl-htpy-hom-species f X y = refl 
```

```agda

is-contr-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : F →ˢ G) → is-contr (Σ (F →ˢ G) (λ g → f ∼ˢ g) )
is-contr-htpy-hom-species f = is-contr-total-Eq-Π (λ X h → f X ~ h) (λ X → is-contr-total-htpy (f X) )

htpy-eq-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → {f g : F →ˢ G} → Id f g → f ∼ˢ g
htpy-eq-hom-species refl X y = refl

is-equiv-htpy-eq-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f g : F →ˢ G) → is-equiv (htpy-eq-hom-species {f = f} {g = g})
is-equiv-htpy-eq-hom-species f = fundamental-theorem-id f (refl-htpy-hom-species f) (is-contr-htpy-hom-species f) (λ g → htpy-eq-hom-species {f = f} {g = g})

eq-htpy-hom-species : {l1 l2 : Level} → {F : species l1} → {G : species l2} → {f g : F →ˢ G} → f ∼ˢ g → Id f g 
eq-htpy-hom-species {f = f} {g = g} = map-inv-is-equiv (is-equiv-htpy-eq-hom-species f g)

```

## Identity morphism

```agda
idˢ : {l : Level} → (F : species l) → F →ˢ F
idˢ F = λ X x → x 
```

## Composition of morphisms

```agda
_∘ˢ_ : {l1 l2 l3 : Level} → {F : species l1} → {G : species l2} → {H : species l3}
                                             → (G →ˢ H) → (F →ˢ G) → (F →ˢ H)
_∘ˢ_ f g = λ X x → f X (g X x)
```

## Unit laws of composition

```agda
left-unit-law-∘ˢ : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : F →ˢ G)
                                                      → Id (idˢ G ∘ˢ f) f
left-unit-law-∘ˢ f = eq-htpy-hom-species (λ X y → refl)

right-unit-law-∘ˢ : {l1 l2 : Level} → {F : species l1} → {G : species l2} → (f : F →ˢ G)
                                                      → Id (f ∘ˢ idˢ F) f
right-unit-law-∘ˢ f = eq-htpy-hom-species (λ X y → refl)

associative-law-∘ˢ : {l1 l2 l3 l4 : Level}
                    → {F : species l1} → {G : species l2} → {H : species l3} → {I : species l4}
                    → (f : F →ˢ G) → (g : G →ˢ H) → (h : H →ˢ I)
                    → Id (h ∘ˢ (g ∘ˢ f)) ((h ∘ˢ g) ∘ˢ f)
associative-law-∘ˢ f g h = eq-htpy-hom-species (λ X y → refl)
```
 
 ## The type of species morphisms is a set

 ```agda
module _
  {l1 l2 : Level} (F : species l1) (G : species l2)
  where


  is-set-→ˢ : is-set (F →ˢ G)
  is-set-→ˢ f g =
    ( is-prop-is-equiv
      ( is-equiv-htpy-eq-hom-species f g)
      ( is-prop-Π (λ X → is-prop-Π (λ x → {!   !}))
    )
    )

  hom-species : UU-Set (lsuc lzero ⊔ l1 ⊔ l2)
  pr1 hom-species = F →ˢ G
  pr2 hom-species = is-set-→ˢ
 ```