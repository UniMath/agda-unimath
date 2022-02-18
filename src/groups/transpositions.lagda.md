# Transpositions


```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.transpositions where

open import univalent-combinatorics
open import univalent-foundations public
```

## Idea

Transpositions are permutations of two elements

## Definitions

```agda
module _
  {l : Level} {X : UU l} (H : has-cardinality X 2)
  where

  swap-two-elements : X ≃ X
  swap-two-elements =
    (equiv-ev-zero-equiv-Fin-two-ℕ H) ∘e
    ( (equiv-precomp-equiv equiv-succ-Fin X) ∘e
      (inv-equiv (equiv-ev-zero-equiv-Fin-two-ℕ H)))

  involution-swap-two-elements : Id (swap-two-elements ∘e swap-two-elements) id-equiv
  involution-swap-two-elements = eq-htpy-equiv refl-htpy ∙
    ( (ap (λ x → (equiv1 ∘e equiv2) ∘e (x ∘e (equiv2 ∘e equiv3))) (left-inverse-law-equiv equiv1)) ∙
      ( (ap (λ x → (equiv1 ∘e equiv2) ∘e x) (left-unit-law-equiv (equiv2 ∘e equiv3))) ∙
        ( (eq-htpy-equiv refl-htpy ∙ (ap (λ x → equiv1 ∘e (x ∘e equiv3)) (eq-htpy-equiv {e = equiv2 ∘e equiv2} λ f → eq-htpy-equiv λ x → ap (map-equiv f) (involution-succ-Fin-two-ℕ x)))) ∙
          ( (ap (λ x → equiv1 ∘e x) (left-unit-law-equiv equiv3) ∙ right-inverse-law-equiv equiv1)))))
    where
    equiv1 : (Fin 2 ≃ X) ≃ X
    equiv1 = equiv-ev-zero-equiv-Fin-two-ℕ H
    equiv2 : (Fin 2 ≃ X) ≃ (Fin 2 ≃ X)
    equiv2 = equiv-precomp-equiv equiv-succ-Fin X
    equiv3 : X ≃ (Fin 2 ≃ X)
    equiv3 = inv-equiv (equiv-ev-zero-equiv-Fin-two-ℕ H)

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin : Id (equiv-precomp-equiv (equiv-succ-Fin {2}) X) id-equiv → empty
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin p' = apply-universal-property-trunc-Prop H empty-Prop λ f → neq-inr-inl
    (map-inv-equiv (pair (ap (map-equiv f)) (is-emb-is-equiv (pr2 f) (inr star) zero-Fin)) (htpy-eq-equiv (htpy-eq-equiv p' f) zero-Fin))
     
  is-not-identity-swap-two-elements : Id swap-two-elements id-equiv → empty
  is-not-identity-swap-two-elements p = is-not-identity-equiv-precomp-equiv-equiv-succ-Fin
    ( (inv (left-unit-law-equiv equiv1) ∙ (ap (λ x → x ∘e equiv1) (inv (left-inverse-law-equiv equiv2)))) ∙
      ( (inv (right-unit-law-equiv ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1))) ∙
        ( (ap (λ x → ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1) ∘e x) ((inv (left-inverse-law-equiv equiv2)))) ∙
          ( (eq-htpy-equiv refl-htpy ∙ (ap (λ x → inv-equiv equiv2 ∘e (x ∘e equiv2) ) p)) ∙
            (ap (λ x → inv-equiv equiv2 ∘e x) (left-unit-law-equiv equiv2) ∙ left-inverse-law-equiv equiv2)))))
    where
    equiv1 : (Fin 2 ≃ X) ≃ (Fin 2 ≃ X)
    equiv1 = equiv-precomp-equiv (equiv-succ-Fin {2}) X
    equiv2 : (Fin 2 ≃ X) ≃ X
    equiv2 = equiv-ev-zero-equiv-Fin-two-ℕ H

module _
  {l : Level} (X : UU l) (P : X → decidable-Prop lzero)
  (H : has-cardinality (Σ X (λ x → type-decidable-Prop (P x))) 2)
  where

  map-transposition' : (x : X) (d : is-decidable (type-decidable-Prop (P x))) → X
  map-transposition' x (inl p) = pr1 (map-equiv (swap-two-elements H) (pair x p))
  map-transposition' x (inr np) = x

  map-transposition : X → X
  map-transposition x = map-transposition' x (is-decidable-type-decidable-Prop (P x))

  involution-map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x))) (d' : is-decidable (type-decidable-Prop (P (map-transposition' x d)))) →
    Id (map-transposition' (map-transposition' x d) d') x
  involution-map-transposition' x (inl p) (inl p') =
    ( ap (λ y → map-transposition' (map-transposition' x (inl p)) (inl y)) (eq-is-prop (pr1 (pr2 (P (map-transposition' x (inl p))))))) ∙
    ( ap pr1 (htpy-eq-equiv (involution-swap-two-elements H) (pair x p)))
  involution-map-transposition' x (inl p) (inr np') = ex-falso (np' (pr2 (map-equiv (swap-two-elements H) (pair x p))))
  involution-map-transposition' x (inr np) (inl p') = ex-falso (np p')
  involution-map-transposition' x (inr np) (inr np') = refl

  involution-map-transposition : (map-transposition ∘ map-transposition) ~ id
  involution-map-transposition x = involution-map-transposition' x (is-decidable-type-decidable-Prop (P x)) (is-decidable-type-decidable-Prop (P (map-transposition' x (is-decidable-type-decidable-Prop (P x)))))

  is-equiv-map-transposition : is-equiv map-transposition
  pr1 (pr1 is-equiv-map-transposition) = map-transposition
  pr2 (pr1 is-equiv-map-transposition) = involution-map-transposition
  pr1 (pr2 is-equiv-map-transposition) = map-transposition
  pr2 (pr2 is-equiv-map-transposition) = involution-map-transposition

  is-not-identity-map-transposition : Id map-transposition id → empty
  is-not-identity-map-transposition f = is-not-identity-swap-two-elements H (eq-htpy-equiv λ {(pair x p) →
    eq-pair-Σ
      ((ap (λ q → map-transposition' x q) (eq-is-prop (is-prop-is-decidable (pr1 (pr2 (P x)))) {y = is-decidable-type-decidable-Prop (P x)})) ∙ htpy-eq f x)
      (eq-is-prop (pr1 (pr2 (P x))))})
```
