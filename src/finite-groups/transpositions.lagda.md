# Transpositions


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.transpositions where

open import univalent-combinatorics
open import univalent-foundations
open import foundation.lists using (list; fold-list; map-list)
```

## Idea

Transpositions are permutations of two elements

## Definitions

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → decidable-Prop l2)
  (H : has-cardinality (Σ X (λ x → type-decidable-Prop (P x))) 2)
  where

  map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x))) → X
  map-transposition' x (inl p) =
    pr1 (map-equiv (swap-two-elements H) (pair x p))
  map-transposition' x (inr np) = x

  map-transposition : X → X
  map-transposition x =
    map-transposition' x (is-decidable-type-decidable-Prop (P x))

  is-involution-map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x)))
    (d' : is-decidable (type-decidable-Prop (P (map-transposition' x d)))) →
    Id (map-transposition' (map-transposition' x d) d') x
  is-involution-map-transposition' x (inl p) (inl p') =
    ( ap
      ( λ y → map-transposition' (map-transposition' x (inl p)) (inl y))
      ( eq-is-prop
        ( is-prop-type-decidable-Prop (P (map-transposition' x (inl p)))))) ∙
    ( ap pr1 (is-involution-aut-2-element-type H (swap-two-elements H) (pair x p)))
  is-involution-map-transposition' x (inl p) (inr np') =
    ex-falso (np' (pr2 (map-equiv (swap-two-elements H) (pair x p))))
  is-involution-map-transposition' x (inr np) (inl p') = ex-falso (np p')
  is-involution-map-transposition' x (inr np) (inr np') = refl

  is-involution-map-transposition : (map-transposition ∘ map-transposition) ~ id
  is-involution-map-transposition x =
    is-involution-map-transposition' x
      ( is-decidable-type-decidable-Prop (P x))
      ( is-decidable-type-decidable-Prop
        ( P (map-transposition' x (is-decidable-type-decidable-Prop (P x)))))

  is-equiv-map-transposition : is-equiv map-transposition
  pr1 (pr1 is-equiv-map-transposition) = map-transposition
  pr2 (pr1 is-equiv-map-transposition) = is-involution-map-transposition
  pr1 (pr2 is-equiv-map-transposition) = map-transposition
  pr2 (pr2 is-equiv-map-transposition) = is-involution-map-transposition

  equiv-map-transposition : X ≃ X
  pr1 equiv-map-transposition = map-transposition
  pr2 equiv-map-transposition = is-equiv-map-transposition

  is-not-identity-map-transposition : Id map-transposition id → empty
  is-not-identity-map-transposition f =
    is-not-identity-swap-two-elements H
      ( eq-htpy-equiv
        ( λ { (pair x p) →
              eq-pair-Σ
                ( ( ap
                    ( map-transposition' x)
                    ( eq-is-prop
                      ( is-prop-is-decidable
                        ( is-prop-type-decidable-Prop (P x)))
                        { y =
                          is-decidable-type-decidable-Prop (P x)})) ∙
                  ( htpy-eq f x))
                ( eq-is-prop (is-prop-type-decidable-Prop (P x)))}))

module _
  {l : Level} {X : UU l} (H : has-decidable-equality X)
  where

  transposition-two-elements : (x y : X) → ¬ (Id x y) →
    Σ (X → decidable-Prop l) (λ P → has-cardinality (Σ X (λ x → type-decidable-Prop (P x))) 2)
  pr1 (pr1 (transposition-two-elements x y p) z) = coprod (Id x z) (Id y z)
  pr1 (pr2 (pr1 (transposition-two-elements x y p) z)) =
    is-prop-coprod
      ( λ q r → p (q ∙ inv r))
      ( is-set-type-Set (pair X (is-set-has-decidable-equality H)) x z)
      ( is-set-type-Set (pair X (is-set-has-decidable-equality H)) y z)
  pr2 (pr2 (pr1 (transposition-two-elements x y p) z)) = is-decidable-coprod (H x z) (H y z)
  pr2 (transposition-two-elements x y p) =
    unit-trunc-Prop
      ( pair f (is-equiv-has-inverse inv-f retr-f sec-f))
    where
    f : Fin 2 → Σ X (λ z → type-decidable-Prop (pr1 (transposition-two-elements x y p) z))
    f (inl (inr star)) = pair x (inl refl)
    f (inr star) = pair y (inr refl)
    inv-f : Σ X (λ z → type-decidable-Prop (pr1 (transposition-two-elements x y p) z)) → Fin 2
    inv-f (pair z (inl refl)) = inl (inr star)
    inv-f (pair z (inr refl)) = inr star
    retr-f : (f ∘ inv-f) ~ id
    retr-f (pair z (inl refl)) = refl
    retr-f (pair z (inr refl)) = refl
    sec-f : (inv-f ∘ f) ~ id
    sec-f (inl (inr star)) = refl
    sec-f (inr star) = refl

  left-computation-transposition-two-elements : (x y : X) (p : ¬ (Id x y)) →
    Id
      ( map-transposition
        ( X)
        ( pr1 (transposition-two-elements x y p))
        ( pr2 (transposition-two-elements x y p))
        ( x))
      ( y)
  left-computation-transposition-two-elements x y p
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) x) 
  ... | inl pp =
    ap
      pr1
      ( computation-swap-two-elements
        ( pr2 (transposition-two-elements x y p))
        ( pair x pp)
        ( pair y (inr refl))
        ( λ q → p (ap pr1 q)))
  ... | inr np = ex-falso (np (inl refl))

  right-computation-transposition-two-elements : (x y : X) (p : ¬ (Id x y)) →
    Id
      ( map-transposition
        ( X)
        ( pr1 (transposition-two-elements x y p))
        ( pr2 (transposition-two-elements x y p))
        ( y))
      ( x)
  right-computation-transposition-two-elements x y p
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) y) 
  ... | inl pp =
    ap
      pr1
      ( computation-swap-two-elements
        ( pr2 (transposition-two-elements x y p))
        ( pair y pp)
        ( pair x (inl refl))
        ( λ q → p (ap pr1 (inv q))))
  ... | inr np = ex-falso (np (inr refl))
```
## Properties

### Every permutation of a finite set can be described as a product of transpositions

```agda
module _
  {l1 l2 : Level} (X : UU l1)
  where

  permutation-list-transpositions :
    ( list
      ( Σ
        ( X → decidable-Prop l2)
        ( λ P → has-cardinality (Σ X (λ x → type-decidable-Prop (P x))) 2))) →
    ( X ≃ X)
  permutation-list-transpositions =
    fold-list id-equiv λ (pair P H) e → (equiv-map-transposition X P H) ∘e e

Fin-succ-Fin-transposition : (n : ℕ) → 
  ( Σ
    ( Fin n → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin n) (λ x → type-decidable-Prop (P x))) 2)) → 
    ( Σ
      ( Fin (succ-ℕ n) → decidable-Prop lzero)
      ( λ P → has-cardinality (Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (P x))) 2))
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inl x) = P x
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inr x) =
  pair empty (pair is-prop-empty is-decidable-empty)
pr2 (Fin-succ-Fin-transposition n (pair P H)) =
  apply-universal-property-trunc-Prop
    ( H)
    ( pair
      ( has-cardinality
        ( Σ
          ( Fin (succ-ℕ n))
          ( λ x → type-decidable-Prop (pr1 (Fin-succ-Fin-transposition n (pair P H)) x)))
        ( 2))
      ( is-prop-type-trunc-Prop))
    ( λ h →
      unit-trunc-Prop
        ( (pair f (is-equiv-has-inverse inv-f retr-f sec-f)) ∘e
          ( inv-right-unit-law-coprod-is-empty
            ( Σ (Fin n)
              ( λ x → type-decidable-Prop (P x)))
            ( Σ unit (λ x → empty)) map-right-absorption-prod ∘e h)))
  where
  f : coprod (Σ (Fin n) (λ x → type-decidable-Prop (P x)))
    (Σ unit (λ x → empty)) →
    Σ (Fin (succ-ℕ n))
    (λ x →
       type-decidable-Prop
       (pr1 (Fin-succ-Fin-transposition n (pair P H)) x))
  f (inl (pair x p)) = pair (inl x) p
  inv-f : Σ (Fin (succ-ℕ n))
    (λ x →
       type-decidable-Prop
       (pr1 (Fin-succ-Fin-transposition n (pair P H)) x)) →
    coprod (Σ (Fin n) (λ x → type-decidable-Prop (P x)))
      (Σ unit (λ x → empty)) 
  inv-f (pair (inl x) p) = inl (pair x p)
  retr-f : (f ∘ inv-f) ~ id
  retr-f (pair (inl x) p) = refl
  sec-f : (inv-f ∘ f) ~ id
  sec-f (inl (pair x p)) = refl

list-transpositions-permutation-Fin' : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
  (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
  ( list
    ( Σ
      ( Fin (succ-ℕ n) → decidable-Prop lzero)
      ( λ P → has-cardinality (Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (P x))) 2)))
list-transpositions-permutation-Fin' zero-ℕ f x p = nil
list-transpositions-permutation-Fin' (succ-ℕ n) f (inl x) p =
  cons
    ( t)
    ( map-list
      ( Fin-succ-Fin-transposition (succ-ℕ n))
      ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x))) 2))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' =
    map-inv-equiv
      ( extend-permutation-Fin-n (succ-ℕ n))
      ( pair
        ( equiv-map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
        ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
          right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl))
list-transpositions-permutation-Fin' (succ-ℕ n) f (inr star) p =
  map-list
    ( Fin-succ-Fin-transposition (succ-ℕ n))
    ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
  where
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' = map-inv-equiv (extend-permutation-Fin-n (succ-ℕ n)) (pair f p)

list-transpositions-permutation-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
  ( list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P → has-cardinality (Σ (Fin n) (λ x → type-decidable-Prop (P x))) 2)))
list-transpositions-permutation-Fin zero-ℕ f = nil
list-transpositions-permutation-Fin (succ-ℕ n) f = list-transpositions-permutation-Fin' n f (map-equiv f (inr star)) refl
```
