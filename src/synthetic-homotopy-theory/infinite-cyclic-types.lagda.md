# Infinite cyclic types

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module synthetic-homotopy-theory.infinite-cyclic-types where

open import elementary-number-theory.addition-integers using
  ( equiv-add-ℤ; add-ℤ; right-successor-law-add-ℤ; left-inverse-law-add-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; succ-ℤ; zero-ℤ; ℤ-Pointed-Type-With-Aut; neg-ℤ; ℤ-Endo;
    is-initial-ℤ-Pointed-Type-With-Aut)
open import elementary-number-theory.natural-numbers using (zero-ℕ)

open import foundation.contractible-maps using (is-equiv-is-contr-map)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; eq-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-property-is-equiv; is-equiv-htpy; is-equiv-id; _∘e_;
    map-equiv; equiv-postcomp-equiv; equiv-ap)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.homotopies using (refl-htpy; _~_)
open import foundation.identity-types using (Id; ap; refl; equiv-concat')
open import foundation.propositional-truncations using (unit-trunc-Prop)
open import foundation.propositions using (is-proof-irrelevant-is-prop)
open import foundation.raising-universe-levels using
  ( raise; map-raise; map-inv-raise; equiv-raise)
open import foundation.type-arithmetic-dependent-pair-types using
  ( right-unit-law-Σ-is-contr; equiv-right-swap-Σ; assoc-Σ)
open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.pointed-types using (Pointed-Type)
open import structured-types.pointed-types-equipped-with-automorphisms using
  ( hom-Pointed-Type-With-Aut)
open import structured-types.types-equipped-with-endomorphisms

open import synthetic-homotopy-theory.loop-spaces using (type-Ω)

open import univalent-combinatorics.cyclic-types using
  ( Cyclic-Type; ℤ-Mod-Cyclic-Type; Cyclic-Type-Pointed-Type; endo-Cyclic-Type;
    type-Cyclic-Type; endomorphism-Cyclic-Type; equiv-Cyclic-Type;
    id-equiv-Cyclic-Type; equiv-eq-Cyclic-Type;
    is-contr-total-equiv-Cyclic-Type; is-equiv-equiv-eq-Cyclic-Type;
    extensionality-Cyclic-Type)
```

```agda
Infinite-Cyclic-Type : (l : Level) → UU (lsuc l)
Infinite-Cyclic-Type l = Cyclic-Type l zero-ℕ 

ℤ-Infinite-Cyclic-Type : Infinite-Cyclic-Type lzero
ℤ-Infinite-Cyclic-Type = ℤ-Mod-Cyclic-Type zero-ℕ

Infinite-Cyclic-Type-Pointed-Type : Pointed-Type (lsuc lzero)
Infinite-Cyclic-Type-Pointed-Type = Cyclic-Type-Pointed-Type zero-ℕ

module _
  {l : Level} (X : Infinite-Cyclic-Type l)
  where

  endo-Infinite-Cyclic-Type : Endo l
  endo-Infinite-Cyclic-Type = endo-Cyclic-Type zero-ℕ X
  
  type-Infinite-Cyclic-Type : UU l
  type-Infinite-Cyclic-Type = type-Cyclic-Type zero-ℕ X
  
  endomorphism-Infinite-Cyclic-Type :
    type-Infinite-Cyclic-Type → type-Infinite-Cyclic-Type
  endomorphism-Infinite-Cyclic-Type = endomorphism-Cyclic-Type zero-ℕ X

  mere-equiv-ℤ-Infinite-Cyclic-Type :
    mere-equiv-Endo ℤ-Endo endo-Infinite-Cyclic-Type
  mere-equiv-ℤ-Infinite-Cyclic-Type = pr2 X
  
module _
  (l : Level)
  where

  point-Infinite-Cyclic-Type : Infinite-Cyclic-Type l
  pr1 (pr1 point-Infinite-Cyclic-Type) = raise l ℤ
  pr2 (pr1 point-Infinite-Cyclic-Type) = (map-raise ∘ succ-ℤ) ∘ map-inv-raise
  pr2 point-Infinite-Cyclic-Type =
    unit-trunc-Prop (pair (equiv-raise l ℤ) refl-htpy)

  Infinite-Cyclic-Type-Pointed-Type-Level : Pointed-Type (lsuc l)
  pr1 Infinite-Cyclic-Type-Pointed-Type-Level = Infinite-Cyclic-Type l
  pr2 Infinite-Cyclic-Type-Pointed-Type-Level = point-Infinite-Cyclic-Type

module _
  {l1 : Level} (X : Infinite-Cyclic-Type l1) 
  where
  
  equiv-Infinite-Cyclic-Type :
    {l2 : Level} → Infinite-Cyclic-Type l2 → UU (l1 ⊔ l2)
  equiv-Infinite-Cyclic-Type = equiv-Cyclic-Type zero-ℕ X

  id-equiv-Infinite-Cyclic-Type : equiv-Infinite-Cyclic-Type X
  id-equiv-Infinite-Cyclic-Type = id-equiv-Cyclic-Type zero-ℕ X

  equiv-eq-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → Id X Y → equiv-Infinite-Cyclic-Type Y
  equiv-eq-Infinite-Cyclic-Type = equiv-eq-Cyclic-Type zero-ℕ X
  
  is-contr-total-equiv-Infinite-Cyclic-Type :
    is-contr (Σ (Infinite-Cyclic-Type l1) equiv-Infinite-Cyclic-Type)
  is-contr-total-equiv-Infinite-Cyclic-Type =
    is-contr-total-equiv-Cyclic-Type zero-ℕ X

  is-equiv-equiv-eq-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → is-equiv (equiv-eq-Infinite-Cyclic-Type Y)
  is-equiv-equiv-eq-Infinite-Cyclic-Type =
    is-equiv-equiv-eq-Cyclic-Type zero-ℕ X

  extensionality-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → Id X Y ≃ equiv-Infinite-Cyclic-Type Y
  extensionality-Infinite-Cyclic-Type = extensionality-Cyclic-Type zero-ℕ X

module _
  where
  
  map-left-factor-compute-Ω-Infinite-Cyclic-Type :
    equiv-Infinite-Cyclic-Type ℤ-Infinite-Cyclic-Type ℤ-Infinite-Cyclic-Type → ℤ
  map-left-factor-compute-Ω-Infinite-Cyclic-Type e =
    map-equiv-Endo ℤ-Endo ℤ-Endo e zero-ℤ

  abstract
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Type :
      is-equiv map-left-factor-compute-Ω-Infinite-Cyclic-Type
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Type =
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
                    ( is-property-is-equiv (pr1 f))
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

  equiv-left-factor-compute-Ω-Infinite-Cyclic-Type :
    equiv-Infinite-Cyclic-Type
      ℤ-Infinite-Cyclic-Type
      ℤ-Infinite-Cyclic-Type ≃ ℤ
  pr1 equiv-left-factor-compute-Ω-Infinite-Cyclic-Type =
    map-left-factor-compute-Ω-Infinite-Cyclic-Type
  pr2 equiv-left-factor-compute-Ω-Infinite-Cyclic-Type =
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Type

  compute-Ω-Infinite-Cyclic-Type :
    type-Ω (Infinite-Cyclic-Type-Pointed-Type) ≃ ℤ
  compute-Ω-Infinite-Cyclic-Type =
    ( equiv-left-factor-compute-Ω-Infinite-Cyclic-Type) ∘e
    ( extensionality-Infinite-Cyclic-Type
        ℤ-Infinite-Cyclic-Type
        ℤ-Infinite-Cyclic-Type)

-- Infinite-Cyclic-Type-𝕊¹ : 𝕊¹ → Infinite-Cyclic-Type
-- pr1 (pr1 (Infinite-Cyclic-Type-𝕊¹ x)) = Id x x
-- pr2 (pr1 (Infinite-Cyclic-Type-𝕊¹ x)) = {!!}
-- pr2 (Infinite-Cyclic-Type-𝕊¹ x) = {!!}

```
