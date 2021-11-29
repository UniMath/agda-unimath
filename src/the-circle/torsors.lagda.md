---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module the-circle.torsors where

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

  equiv-id-Endo : equiv-Endo X X
  pr1 equiv-id-Endo = equiv-id
  pr2 equiv-id-Endo = refl-htpy
  
  refl-mere-equiv-Endo : mere-equiv-Endo X X
  refl-mere-equiv-Endo = unit-trunc-Prop equiv-id-Endo

  equiv-eq-Endo : (Y : Endo l1) → Id X Y → equiv-Endo X Y
  equiv-eq-Endo .X refl = equiv-id-Endo
  
  is-contr-total-equiv-Endo : is-contr (Σ (Endo l1) (equiv-Endo X))
  is-contr-total-equiv-Endo =
    is-contr-total-Eq-structure
      ( λ Y f e → (map-equiv e ∘ endomorphism-Endo X) ~ (f ∘ map-equiv e))
      ( is-contr-total-equiv (type-Endo X))
      ( pair (type-Endo X) equiv-id)
      ( is-contr-total-htpy (endomorphism-Endo X))

  is-equiv-equiv-eq-Endo : (Y : Endo l1) → is-equiv (equiv-eq-Endo Y)
  is-equiv-equiv-eq-Endo =
    fundamental-theorem-id X
      equiv-id-Endo
      is-contr-total-equiv-Endo
      equiv-eq-Endo

  eq-equiv-Endo : (Y : Endo l1) → equiv-Endo X Y → Id X Y
  eq-equiv-Endo Y = map-inv-is-equiv (is-equiv-equiv-eq-Endo Y)

module _
  {l1 : Level} (X : Endo l1)
  where
  
  Endo-Torsor : UU (lsuc l1)
  Endo-Torsor = Σ (Endo l1) (mere-equiv-Endo X)

  endo-Endo-Torsor : Endo-Torsor → Endo l1
  endo-Endo-Torsor = pr1

  type-Endo-Torsor : Endo-Torsor → UU l1
  type-Endo-Torsor = pr1 ∘ endo-Endo-Torsor

  endomorphism-Endo-Torsor :
    (T : Endo-Torsor) → type-Endo-Torsor T → type-Endo-Torsor T
  endomorphism-Endo-Torsor T = pr2 (endo-Endo-Torsor T)

  mere-equiv-Endo-Torsor :
    (T : Endo-Torsor) → mere-equiv-Endo X (endo-Endo-Torsor T)
  mere-equiv-Endo-Torsor T = pr2 T

  canonical-Endo-Torsor : Endo-Torsor
  pr1 canonical-Endo-Torsor = X
  pr2 canonical-Endo-Torsor = refl-mere-equiv-Endo X

module _
  {l1 : Level} (X : Endo l1)
  where

  equiv-Endo-Torsor : (T S : Endo-Torsor X) → UU l1
  equiv-Endo-Torsor T S =
    equiv-Endo (endo-Endo-Torsor X T) (endo-Endo-Torsor X S)

  equiv-id-Endo-Torsor : (T : Endo-Torsor X) → equiv-Endo-Torsor T T
  equiv-id-Endo-Torsor T = equiv-id-Endo (endo-Endo-Torsor X T)

  equiv-eq-Endo-Torsor : (T S : Endo-Torsor X) → Id T S → equiv-Endo-Torsor T S
  equiv-eq-Endo-Torsor T .T refl = equiv-id-Endo-Torsor T
  
  is-contr-total-equiv-Endo-Torsor :
    is-contr
      ( Σ ( Endo-Torsor X)
          ( λ T → equiv-Endo-Torsor (canonical-Endo-Torsor X) T))
  is-contr-total-equiv-Endo-Torsor =
    is-contr-total-Eq-substructure
      ( is-contr-total-equiv-Endo X)
      ( λ Y → is-prop-type-trunc-Prop)
      ( X)
      ( equiv-id-Endo X)
      ( refl-mere-equiv-Endo X)

  is-equiv-equiv-eq-Endo-Torsor :
    (T : Endo-Torsor X) →
    is-equiv (equiv-eq-Endo-Torsor (canonical-Endo-Torsor X) T)
  is-equiv-equiv-eq-Endo-Torsor =
    fundamental-theorem-id
      ( canonical-Endo-Torsor X)
      ( equiv-id-Endo-Torsor (canonical-Endo-Torsor X))
      ( is-contr-total-equiv-Endo-Torsor)
      ( equiv-eq-Endo-Torsor (canonical-Endo-Torsor X))

ℤ-Torsor : UU (lsuc lzero)
ℤ-Torsor = Endo-Torsor ℤ-Endo

module _
  (X : ℤ-Torsor)
  where

  endo-ℤ-Torsor : Endo lzero
  endo-ℤ-Torsor = pr1 X
  
  type-ℤ-Torsor : UU lzero
  type-ℤ-Torsor = pr1 (pr1 X)
  
  endomorphism-ℤ-Torsor : type-ℤ-Torsor → type-ℤ-Torsor
  endomorphism-ℤ-Torsor = pr2 (pr1 X)
  
module _
  where

  canonical-ℤ-Torsor : ℤ-Torsor
  pr1 canonical-ℤ-Torsor = ℤ-Endo
  pr2 canonical-ℤ-Torsor = refl-mere-equiv-Endo ℤ-Endo

  ℤ-Torsor-Pointed-Type : Pointed-Type (lsuc lzero)
  pr1 ℤ-Torsor-Pointed-Type = ℤ-Torsor
  pr2 ℤ-Torsor-Pointed-Type = canonical-ℤ-Torsor

  equiv-ℤ-Torsor : (T S : ℤ-Torsor) → UU lzero
  equiv-ℤ-Torsor = equiv-Endo-Torsor ℤ-Endo

  equiv-id-ℤ-Torsor : (T : ℤ-Torsor) → equiv-ℤ-Torsor T T
  equiv-id-ℤ-Torsor = equiv-id-Endo-Torsor ℤ-Endo

  equiv-eq-ℤ-Torsor : (T S : ℤ-Torsor) → Id T S → equiv-ℤ-Torsor T S
  equiv-eq-ℤ-Torsor = equiv-eq-Endo-Torsor ℤ-Endo
  
  is-contr-total-equiv-ℤ-Torsor :
    is-contr
      ( Σ ( ℤ-Torsor)
          ( λ T → equiv-ℤ-Torsor (canonical-ℤ-Torsor) T))
  is-contr-total-equiv-ℤ-Torsor =
    is-contr-total-equiv-Endo-Torsor ℤ-Endo

  is-equiv-equiv-eq-ℤ-Torsor :
    (T : ℤ-Torsor) →
    is-equiv (equiv-eq-ℤ-Torsor (canonical-ℤ-Torsor) T)
  is-equiv-equiv-eq-ℤ-Torsor = is-equiv-equiv-eq-Endo-Torsor ℤ-Endo

  equiv-equiv-eq-ℤ-Torsor :
    (T : ℤ-Torsor) →
    Id canonical-ℤ-Torsor T ≃ equiv-ℤ-Torsor canonical-ℤ-Torsor T
  pr1 (equiv-equiv-eq-ℤ-Torsor T) = equiv-eq-ℤ-Torsor canonical-ℤ-Torsor T
  pr2 (equiv-equiv-eq-ℤ-Torsor T) = is-equiv-equiv-eq-ℤ-Torsor T

  map-left-factor-compute-Ω-ℤ-Torsor :
    equiv-ℤ-Torsor canonical-ℤ-Torsor canonical-ℤ-Torsor → ℤ
  map-left-factor-compute-Ω-ℤ-Torsor e = map-equiv (pr1 e) zero-ℤ

  is-equiv-map-left-factor-compute-Ω-ℤ-Torsor :
    is-equiv map-left-factor-compute-Ω-ℤ-Torsor
  is-equiv-map-left-factor-compute-Ω-ℤ-Torsor =
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

  equiv-left-factor-compute-Ω-ℤ-Torsor :
    equiv-ℤ-Torsor canonical-ℤ-Torsor canonical-ℤ-Torsor ≃ ℤ
  pr1 equiv-left-factor-compute-Ω-ℤ-Torsor = map-left-factor-compute-Ω-ℤ-Torsor
  pr2 equiv-left-factor-compute-Ω-ℤ-Torsor =
    is-equiv-map-left-factor-compute-Ω-ℤ-Torsor

  compute-Ω-ℤ-Torsor : type-Ω ℤ-Torsor-Pointed-Type ≃ ℤ
  compute-Ω-ℤ-Torsor =
    ( equiv-left-factor-compute-Ω-ℤ-Torsor) ∘e
    ( equiv-equiv-eq-ℤ-Torsor canonical-ℤ-Torsor)

```
