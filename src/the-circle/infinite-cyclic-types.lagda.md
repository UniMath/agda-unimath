
---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module the-circle.infinite-cyclic-types where

open import the-circle.universal-cover public
open import the-circle.integers public

Endo : (l : Level) → UU (lsuc l)
Endo l = Σ (UU l) (λ X → X → X)

module _
  {l : Level} (X : Endo l)
  where

  type-Endo : UU l
  type-Endo = pr1 X

  endomorphism-Endo : type-Endo → type-Endo
  endomorphism-Endo = pr2 X

ℤ-Endo : Endo lzero
pr1 ℤ-Endo = ℤ
pr2 ℤ-Endo = succ-ℤ

module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  equiv-Endo : UU (l1 ⊔ l2)
  equiv-Endo =
    Σ ( type-Endo X ≃ type-Endo Y)
      ( λ e →
        ( map-equiv e ∘ endomorphism-Endo X) ~
        ( endomorphism-Endo Y ∘ map-equiv e))

  mere-equiv-Endo : UU (l1 ⊔ l2)
  mere-equiv-Endo = type-trunc-Prop equiv-Endo

module _
  {l1 : Level} (X : Endo l1)
  where

  id-equiv-Endo : equiv-Endo X X
  pr1 id-equiv-Endo = id-equiv
  pr2 id-equiv-Endo = refl-htpy
  
  refl-mere-equiv-Endo : mere-equiv-Endo X X
  refl-mere-equiv-Endo = unit-trunc-Prop id-equiv-Endo

  equiv-eq-Endo : (Y : Endo l1) → Id X Y → equiv-Endo X Y
  equiv-eq-Endo .X refl = id-equiv-Endo
  
  is-contr-total-equiv-Endo : is-contr (Σ (Endo l1) (equiv-Endo X))
  is-contr-total-equiv-Endo =
    is-contr-total-Eq-structure
      ( λ Y f e → (map-equiv e ∘ endomorphism-Endo X) ~ (f ∘ map-equiv e))
      ( is-contr-total-equiv (type-Endo X))
      ( pair (type-Endo X) id-equiv)
      ( is-contr-total-htpy (endomorphism-Endo X))

  is-equiv-equiv-eq-Endo : (Y : Endo l1) → is-equiv (equiv-eq-Endo Y)
  is-equiv-equiv-eq-Endo =
    fundamental-theorem-id X
      id-equiv-Endo
      is-contr-total-equiv-Endo
      equiv-eq-Endo

  eq-equiv-Endo : (Y : Endo l1) → equiv-Endo X Y → Id X Y
  eq-equiv-Endo Y = map-inv-is-equiv (is-equiv-equiv-eq-Endo Y)

module _
  {l1 : Level} (X : Endo l1)
  where
  
  Component-Endo : UU (lsuc l1)
  Component-Endo = Σ (Endo l1) (mere-equiv-Endo X)

  endo-Component-Endo : Component-Endo → Endo l1
  endo-Component-Endo = pr1

  type-Component-Endo : Component-Endo → UU l1
  type-Component-Endo = pr1 ∘ endo-Component-Endo

  endomorphism-Component-Endo :
    (T : Component-Endo) → type-Component-Endo T → type-Component-Endo T
  endomorphism-Component-Endo T = pr2 (endo-Component-Endo T)

  mere-equiv-Component-Endo :
    (T : Component-Endo) → mere-equiv-Endo X (endo-Component-Endo T)
  mere-equiv-Component-Endo T = pr2 T

  canonical-Component-Endo : Component-Endo
  pr1 canonical-Component-Endo = X
  pr2 canonical-Component-Endo = refl-mere-equiv-Endo X

module _
  {l1 : Level} (X : Endo l1)
  where

  equiv-Component-Endo : (T S : Component-Endo X) → UU l1
  equiv-Component-Endo T S =
    equiv-Endo (endo-Component-Endo X T) (endo-Component-Endo X S)

  id-equiv-Component-Endo : (T : Component-Endo X) → equiv-Component-Endo T T
  id-equiv-Component-Endo T = id-equiv-Endo (endo-Component-Endo X T)

  equiv-eq-Component-Endo :
    (T S : Component-Endo X) → Id T S → equiv-Component-Endo T S
  equiv-eq-Component-Endo T .T refl = id-equiv-Component-Endo T
  
  is-contr-total-equiv-Component-Endo :
    is-contr
      ( Σ ( Component-Endo X)
          ( λ T → equiv-Component-Endo (canonical-Component-Endo X) T))
  is-contr-total-equiv-Component-Endo =
    is-contr-total-Eq-substructure
      ( is-contr-total-equiv-Endo X)
      ( λ Y → is-prop-type-trunc-Prop)
      ( X)
      ( id-equiv-Endo X)
      ( refl-mere-equiv-Endo X)

  is-equiv-equiv-eq-Component-Endo :
    (T : Component-Endo X) →
    is-equiv (equiv-eq-Component-Endo (canonical-Component-Endo X) T)
  is-equiv-equiv-eq-Component-Endo =
    fundamental-theorem-id
      ( canonical-Component-Endo X)
      ( id-equiv-Component-Endo (canonical-Component-Endo X))
      ( is-contr-total-equiv-Component-Endo)
      ( equiv-eq-Component-Endo (canonical-Component-Endo X))

Infinite-Cyclic : (l : Level) → UU (lsuc l)
Infinite-Cyclic l = Σ (Endo l) (λ X → mere-equiv-Endo ℤ-Endo X)

ℤ-Infinite-Cyclic : Infinite-Cyclic lzero
pr1 ℤ-Infinite-Cyclic = ℤ-Endo
pr2 ℤ-Infinite-Cyclic = refl-mere-equiv-Endo ℤ-Endo

Infinite-Cyclic-Pointed-Type : Pointed-Type (lsuc lzero)
pr1 Infinite-Cyclic-Pointed-Type = Infinite-Cyclic lzero
pr2 Infinite-Cyclic-Pointed-Type = ℤ-Infinite-Cyclic

module _
  {l : Level} (X : Infinite-Cyclic l)
  where

  endo-Infinite-Cyclic : Endo l
  endo-Infinite-Cyclic = pr1 X
  
  type-Infinite-Cyclic : UU l
  type-Infinite-Cyclic = pr1 (pr1 X)
  
  endomorphism-Infinite-Cyclic :
    type-Infinite-Cyclic → type-Infinite-Cyclic
  endomorphism-Infinite-Cyclic = pr2 (pr1 X)

  mere-equiv-ℤ-Infinite-Cyclic : mere-equiv-Endo ℤ-Endo endo-Infinite-Cyclic
  mere-equiv-ℤ-Infinite-Cyclic = pr2 X
  
module _
  (l : Level)
  where

  point-Infinite-Cyclic : Infinite-Cyclic l
  pr1 (pr1 point-Infinite-Cyclic) = raise l ℤ
  pr2 (pr1 point-Infinite-Cyclic) = (map-raise ∘ succ-ℤ) ∘ map-inv-raise
  pr2 point-Infinite-Cyclic =
    unit-trunc-Prop (pair (equiv-raise l ℤ) refl-htpy)

  Infinite-Cyclic-Pointed-Type-Level : Pointed-Type (lsuc l)
  pr1 Infinite-Cyclic-Pointed-Type-Level = Infinite-Cyclic l
  pr2 Infinite-Cyclic-Pointed-Type-Level = point-Infinite-Cyclic

module _
  {l1 : Level} (X : Infinite-Cyclic l1) 
  where
  
  equiv-Infinite-Cyclic : {l2 : Level} → Infinite-Cyclic l2 → UU (l1 ⊔ l2)
  equiv-Infinite-Cyclic Y =
    equiv-Endo (endo-Infinite-Cyclic X) (endo-Infinite-Cyclic Y)

  id-equiv-Infinite-Cyclic : equiv-Infinite-Cyclic X
  id-equiv-Infinite-Cyclic = id-equiv-Endo (endo-Infinite-Cyclic X)

  equiv-eq-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → Id X Y → equiv-Infinite-Cyclic Y
  equiv-eq-Infinite-Cyclic .X refl = id-equiv-Infinite-Cyclic
  
  is-contr-total-equiv-Infinite-Cyclic :
    is-contr (Σ (Infinite-Cyclic l1) equiv-Infinite-Cyclic)
  is-contr-total-equiv-Infinite-Cyclic =
    is-contr-total-Eq-substructure
      ( is-contr-total-equiv-Endo (endo-Infinite-Cyclic X))
      ( λ Y → is-prop-type-trunc-Prop)
      ( endo-Infinite-Cyclic X)
      ( id-equiv-Endo (endo-Infinite-Cyclic X))
      ( mere-equiv-ℤ-Infinite-Cyclic X)

  is-equiv-equiv-eq-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → is-equiv (equiv-eq-Infinite-Cyclic Y)
  is-equiv-equiv-eq-Infinite-Cyclic =
    fundamental-theorem-id X
      id-equiv-Infinite-Cyclic
      is-contr-total-equiv-Infinite-Cyclic
      equiv-eq-Infinite-Cyclic

  extensionality-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → Id X Y ≃ equiv-Infinite-Cyclic Y
  pr1 (extensionality-Infinite-Cyclic Y) = equiv-eq-Infinite-Cyclic Y
  pr2 (extensionality-Infinite-Cyclic Y) = is-equiv-equiv-eq-Infinite-Cyclic Y

module _
  where
  
  map-left-factor-compute-Ω-Infinite-Cyclic :
    equiv-Infinite-Cyclic ℤ-Infinite-Cyclic ℤ-Infinite-Cyclic → ℤ
  map-left-factor-compute-Ω-Infinite-Cyclic e = map-equiv (pr1 e) zero-ℤ

  abstract
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic :
      is-equiv map-left-factor-compute-Ω-Infinite-Cyclic
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic =
      is-equiv-is-contr-map
        ( λ x →
          is-contr-equiv
            ( hom-Pointed-Type-With-Aut
                ℤ-Pointed-Type-With-Aut
                ℤ-Pointed-Type-With-Aut)
            ( ( right-unit-law-Σ-is-contr
                { B = λ f → is-equiv (pr1 f)}
                ( λ f →
                  is-proof-irrelevant-is-prop
                    ( is-subtype-is-equiv (pr1 f))
                    ( is-equiv-htpy id
                      ( htpy-eq
                        ( ap
                          ( pr1)
                          { x = f}
                          { y = pair id (pair refl refl-htpy)}
                          ( eq-is-contr
                            ( is-initial-ℤ-Pointed-Type-With-Aut
                              ℤ-Pointed-Type-With-Aut))))
                      ( is-equiv-id)))) ∘e
              ( ( equiv-right-swap-Σ) ∘e
                ( ( assoc-Σ
                    ( ℤ ≃ ℤ)
                    ( λ e → Id (map-equiv e zero-ℤ) zero-ℤ)
                    ( λ e →
                      ( map-equiv (pr1 e) ∘ succ-ℤ) ~
                      ( succ-ℤ ∘ map-equiv (pr1 e)))) ∘e
                  ( ( equiv-right-swap-Σ) ∘e
                    ( equiv-Σ
                      ( λ e → Id (map-equiv (pr1 e) zero-ℤ) zero-ℤ)
                      ( equiv-Σ
                        ( λ e → (map-equiv e ∘ succ-ℤ) ~ (succ-ℤ ∘ map-equiv e))
                        ( equiv-postcomp-equiv (equiv-add-ℤ (neg-ℤ x)) ℤ)
                        ( λ e →
                          equiv-map-Π
                            ( λ k →
                              ( equiv-concat'
                                ( add-ℤ (neg-ℤ x) (map-equiv e (succ-ℤ k)))
                                ( right-successor-law-add-ℤ
                                  ( neg-ℤ x)
                                  ( map-equiv e k))) ∘e
                              ( equiv-ap
                                ( equiv-add-ℤ (neg-ℤ x))
                                ( map-equiv e (succ-ℤ k))
                                ( succ-ℤ (map-equiv e k))))))
                      ( λ e →
                        ( equiv-concat'
                          ( add-ℤ (neg-ℤ x) (map-equiv (pr1 e) zero-ℤ))
                          ( left-inverse-law-add-ℤ x)) ∘e
                        ( equiv-ap
                          ( equiv-add-ℤ (neg-ℤ x))
                          ( map-equiv (pr1 e) zero-ℤ)
                          ( x))))))))
            ( is-initial-ℤ-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut))

  equiv-left-factor-compute-Ω-Infinite-Cyclic :
    equiv-Infinite-Cyclic
      ℤ-Infinite-Cyclic
      ℤ-Infinite-Cyclic ≃ ℤ
  pr1 equiv-left-factor-compute-Ω-Infinite-Cyclic =
    map-left-factor-compute-Ω-Infinite-Cyclic
  pr2 equiv-left-factor-compute-Ω-Infinite-Cyclic =
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic

  compute-Ω-Infinite-Cyclic : type-Ω (Infinite-Cyclic-Pointed-Type) ≃ ℤ
  compute-Ω-Infinite-Cyclic =
    ( equiv-left-factor-compute-Ω-Infinite-Cyclic) ∘e
    ( extensionality-Infinite-Cyclic ℤ-Infinite-Cyclic ℤ-Infinite-Cyclic)

-- Infinite-Cyclic-𝕊¹ : 𝕊¹ → Infinite-Cyclic
-- pr1 (pr1 (Infinite-Cyclic-𝕊¹ x)) = Id x x
-- pr2 (pr1 (Infinite-Cyclic-𝕊¹ x)) = {!!}
-- pr2 (Infinite-Cyclic-𝕊¹ x) = {!!}

```
