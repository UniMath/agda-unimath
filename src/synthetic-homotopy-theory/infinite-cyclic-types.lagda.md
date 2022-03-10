# Infinite cyclic types

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module synthetic-homotopy-theory.infinite-cyclic-types where

open import elementary-number-theory.addition-integers using
  ( equiv-add-ℤ; add-ℤ; right-successor-law-add-ℤ; left-inverse-law-add-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; succ-ℤ; zero-ℤ; ℤ-Pointed-Type-With-Aut; neg-ℤ;
    is-initial-ℤ-Pointed-Type-With-Aut)
open import elementary-number-theory.natural-numbers using (zero-ℕ)

open import foundation.automorphisms using (hom-Pointed-Type-With-Aut)
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

open import synthetic-homotopy-theory.cyclic-types using
  ( Cyclic; ℤ-Mod-Cyclic; Cyclic-Pointed-Type; Endo; endo-Cyclic; type-Cyclic;
    endomorphism-Cyclic; mere-equiv-Endo; ℤ-Endo; equiv-Cyclic; id-equiv-Cyclic;
    equiv-eq-Cyclic; is-contr-total-equiv-Cyclic;
    is-equiv-equiv-eq-Cyclic; extensionality-Cyclic; map-equiv-Endo)
open import synthetic-homotopy-theory.loop-spaces using (type-Ω)
open import synthetic-homotopy-theory.pointed-types using
  ( Pointed-Type)
```

```agda
Infinite-Cyclic : (l : Level) → UU (lsuc l)
Infinite-Cyclic l = Cyclic l zero-ℕ 

ℤ-Infinite-Cyclic : Infinite-Cyclic lzero
ℤ-Infinite-Cyclic = ℤ-Mod-Cyclic zero-ℕ

Infinite-Cyclic-Pointed-Type : Pointed-Type (lsuc lzero)
Infinite-Cyclic-Pointed-Type = Cyclic-Pointed-Type zero-ℕ

module _
  {l : Level} (X : Infinite-Cyclic l)
  where

  endo-Infinite-Cyclic : Endo l
  endo-Infinite-Cyclic = endo-Cyclic zero-ℕ X
  
  type-Infinite-Cyclic : UU l
  type-Infinite-Cyclic = type-Cyclic zero-ℕ X
  
  endomorphism-Infinite-Cyclic :
    type-Infinite-Cyclic → type-Infinite-Cyclic
  endomorphism-Infinite-Cyclic = endomorphism-Cyclic zero-ℕ X

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
  equiv-Infinite-Cyclic = equiv-Cyclic zero-ℕ X

  id-equiv-Infinite-Cyclic : equiv-Infinite-Cyclic X
  id-equiv-Infinite-Cyclic = id-equiv-Cyclic zero-ℕ X

  equiv-eq-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → Id X Y → equiv-Infinite-Cyclic Y
  equiv-eq-Infinite-Cyclic = equiv-eq-Cyclic zero-ℕ X
  
  is-contr-total-equiv-Infinite-Cyclic :
    is-contr (Σ (Infinite-Cyclic l1) equiv-Infinite-Cyclic)
  is-contr-total-equiv-Infinite-Cyclic = is-contr-total-equiv-Cyclic zero-ℕ X

  is-equiv-equiv-eq-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → is-equiv (equiv-eq-Infinite-Cyclic Y)
  is-equiv-equiv-eq-Infinite-Cyclic = is-equiv-equiv-eq-Cyclic zero-ℕ X

  extensionality-Infinite-Cyclic :
    (Y : Infinite-Cyclic l1) → Id X Y ≃ equiv-Infinite-Cyclic Y
  extensionality-Infinite-Cyclic = extensionality-Cyclic zero-ℕ X

module _
  where
  
  map-left-factor-compute-Ω-Infinite-Cyclic :
    equiv-Infinite-Cyclic ℤ-Infinite-Cyclic ℤ-Infinite-Cyclic → ℤ
  map-left-factor-compute-Ω-Infinite-Cyclic e =
    map-equiv-Endo ℤ-Endo ℤ-Endo e zero-ℤ

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
