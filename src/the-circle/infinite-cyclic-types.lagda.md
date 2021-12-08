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

  equiv-eq-Component-Endo : (T S : Component-Endo X) → Id T S → equiv-Component-Endo T S
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

UU-Infinite-Cyclic : UU (lsuc lzero)
UU-Infinite-Cyclic = Component-Endo ℤ-Endo

module _
  (X : UU-Infinite-Cyclic)
  where

  endo-UU-Infinite-Cyclic : Endo lzero
  endo-UU-Infinite-Cyclic = pr1 X
  
  type-UU-Infinite-Cyclic : UU lzero
  type-UU-Infinite-Cyclic = pr1 (pr1 X)
  
  endomorphism-UU-Infinite-Cyclic :
    type-UU-Infinite-Cyclic → type-UU-Infinite-Cyclic
  endomorphism-UU-Infinite-Cyclic = pr2 (pr1 X)
  
module _
  where

  canonical-UU-Infinite-Cyclic : UU-Infinite-Cyclic
  pr1 canonical-UU-Infinite-Cyclic = ℤ-Endo
  pr2 canonical-UU-Infinite-Cyclic = refl-mere-equiv-Endo ℤ-Endo

  UU-Infinite-Cyclic-Pointed-Type : Pointed-Type (lsuc lzero)
  pr1 UU-Infinite-Cyclic-Pointed-Type = UU-Infinite-Cyclic
  pr2 UU-Infinite-Cyclic-Pointed-Type = canonical-UU-Infinite-Cyclic

  equiv-UU-Infinite-Cyclic : (T S : UU-Infinite-Cyclic) → UU lzero
  equiv-UU-Infinite-Cyclic = equiv-Component-Endo ℤ-Endo

  id-equiv-UU-Infinite-Cyclic :
    (T : UU-Infinite-Cyclic) → equiv-UU-Infinite-Cyclic T T
  id-equiv-UU-Infinite-Cyclic = id-equiv-Component-Endo ℤ-Endo

  equiv-eq-UU-Infinite-Cyclic :
    (T S : UU-Infinite-Cyclic) → Id T S → equiv-UU-Infinite-Cyclic T S
  equiv-eq-UU-Infinite-Cyclic = equiv-eq-Component-Endo ℤ-Endo
  
  is-contr-total-equiv-UU-Infinite-Cyclic :
    is-contr
      ( Σ ( UU-Infinite-Cyclic)
          ( λ T →
            equiv-UU-Infinite-Cyclic (canonical-UU-Infinite-Cyclic) T))
  is-contr-total-equiv-UU-Infinite-Cyclic =
    is-contr-total-equiv-Component-Endo ℤ-Endo

  is-equiv-equiv-eq-UU-Infinite-Cyclic :
    (T : UU-Infinite-Cyclic) →
    is-equiv (equiv-eq-UU-Infinite-Cyclic (canonical-UU-Infinite-Cyclic) T)
  is-equiv-equiv-eq-UU-Infinite-Cyclic =
    is-equiv-equiv-eq-Component-Endo ℤ-Endo

  equiv-equiv-eq-UU-Infinite-Cyclic :
    (T : UU-Infinite-Cyclic) →
    Id canonical-UU-Infinite-Cyclic T ≃
    equiv-UU-Infinite-Cyclic canonical-UU-Infinite-Cyclic T
  pr1 (equiv-equiv-eq-UU-Infinite-Cyclic T) =
    equiv-eq-UU-Infinite-Cyclic canonical-UU-Infinite-Cyclic T
  pr2 (equiv-equiv-eq-UU-Infinite-Cyclic T) =
    is-equiv-equiv-eq-UU-Infinite-Cyclic T

  map-left-factor-compute-Ω-UU-Infinite-Cyclic :
    ( equiv-UU-Infinite-Cyclic
        canonical-UU-Infinite-Cyclic
        canonical-UU-Infinite-Cyclic) → ℤ
  map-left-factor-compute-Ω-UU-Infinite-Cyclic e = map-equiv (pr1 e) zero-ℤ

  abstract
    is-equiv-map-left-factor-compute-Ω-UU-Infinite-Cyclic :
      is-equiv map-left-factor-compute-Ω-UU-Infinite-Cyclic
    is-equiv-map-left-factor-compute-Ω-UU-Infinite-Cyclic =
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

  equiv-left-factor-compute-Ω-UU-Infinite-Cyclic :
    equiv-UU-Infinite-Cyclic
      canonical-UU-Infinite-Cyclic
      canonical-UU-Infinite-Cyclic ≃ ℤ
  pr1 equiv-left-factor-compute-Ω-UU-Infinite-Cyclic =
    map-left-factor-compute-Ω-UU-Infinite-Cyclic
  pr2 equiv-left-factor-compute-Ω-UU-Infinite-Cyclic =
    is-equiv-map-left-factor-compute-Ω-UU-Infinite-Cyclic

  compute-Ω-UU-Infinite-Cyclic : type-Ω UU-Infinite-Cyclic-Pointed-Type ≃ ℤ
  compute-Ω-UU-Infinite-Cyclic =
    ( equiv-left-factor-compute-Ω-UU-Infinite-Cyclic) ∘e
    ( equiv-equiv-eq-UU-Infinite-Cyclic canonical-UU-Infinite-Cyclic)

-- UU-Infinite-Cyclic-𝕊¹ : 𝕊¹ → UU-Infinite-Cyclic
-- pr1 (pr1 (UU-Infinite-Cyclic-𝕊¹ x)) = Id x x
-- pr2 (pr1 (UU-Infinite-Cyclic-𝕊¹ x)) = {!!}
-- pr2 (UU-Infinite-Cyclic-𝕊¹ x) = {!!}

```
