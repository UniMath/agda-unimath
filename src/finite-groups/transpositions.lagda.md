# Transpositions


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.transpositions where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-injective-inl; is-prop-coprod; neq-inr-inl)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using
  (is-decidable; is-decidable-coprod; is-decidable-empty; is-prop-is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; ex-falso; is-prop-empty)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ; pair-eq-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; htpy-equiv; id-equiv; is-emb-is-equiv; is-equiv;
    is-equiv-has-inverse; right-inverse-law-equiv; map-equiv; map-inv-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functoriality-coproduct-types using (id-map-coprod; map-coprod)
open import foundation.homotopies using (comp-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap)
open import foundation.lists using (cons; list; fold-list; map-list; nil)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop)
open import foundation.sets using (is-set-type-Set; Id-Prop)
open import foundation.type-arithmetic-empty-type using
  ( inv-right-unit-law-coprod-is-empty; map-right-absorption-prod)
open import foundation.unit-type using (star; unit)
open import foundation.universe-levels using (Level; UU; lzero)

open import foundation-core.propositions using (eq-is-prop)
open import foundation-core.homotopies using (_~_; refl-htpy; inv-htpy)

open import univalent-combinatorics.2-element-types using
  ( computation-swap-two-elements; is-involution-aut-2-element-type;
    has-no-fixpoints-swap-two-elements; swap-two-elements; is-not-identity-swap-two-elements)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin; Fin-Set)
open import univalent-combinatorics.equivalences-standard-finite-types using
  ( extend-permutation-Fin-n; comp-extend-permutation-Fin-n; computation-inv-extend-permutation-Fin-n)
open import univalent-combinatorics.finite-types using (has-cardinality)
open import univalent-combinatorics.standard-finite-types using (Fin)
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

  is-transposition : is-equiv map-transposition
  pr1 (pr1 is-transposition) = map-transposition
  pr2 (pr1 is-transposition) = is-involution-map-transposition
  pr1 (pr2 is-transposition) = map-transposition
  pr2 (pr2 is-transposition) = is-involution-map-transposition

  transposition : X ≃ X
  pr1 transposition = map-transposition
  pr2 transposition = is-transposition

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

  not-computation-transposition-two-elements : (x y z : X) (p : ¬ (Id x y)) →
    ¬ (Id x z) → ¬ (Id y z) →
    Id
      ( map-transposition
        ( X)
        ( pr1 (transposition-two-elements x y p))
        ( pr2 (transposition-two-elements x y p))
        ( z))
      ( z)
  not-computation-transposition-two-elements x y z p q r 
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) z) 
  ... | inl (inl h) = ex-falso (q h)
  ... | inl (inr h) = ex-falso (r h)
  ... | inr np = refl
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
    fold-list id-equiv λ (pair P H) e → (transposition X P H) ∘e e

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

correct-Fin-succ-Fin-transposition : (n : ℕ) → 
  (t : Σ
    ( Fin n → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin n) (λ x → type-decidable-Prop (P x))) 2)) → 
  htpy-equiv
    ( transposition
      ( Fin (succ-ℕ n))
      ( pr1 (Fin-succ-Fin-transposition n t))
      ( pr2 (Fin-succ-Fin-transposition n t)))
    ( pr1
      ( map-equiv
        ( extend-permutation-Fin-n n)
        ( transposition (Fin n) (pr1 t) (pr2 t)))) 
correct-Fin-succ-Fin-transposition n t (inl x) with is-decidable-type-decidable-Prop (pr1 t x)
correct-Fin-succ-Fin-transposition n t (inl x) | inl p =
    ap
      ( pr1)
      ( computation-swap-two-elements
        ( pr2 (Fin-succ-Fin-transposition n t))
        ( pair (inl x) p)
        ( pair
          ( inl (pr1 (map-equiv (swap-two-elements (pr2 t)) (pair x p))))
          ( pr2 (map-equiv (swap-two-elements (pr2 t)) (pair x p))))
        ( λ eq →
          has-no-fixpoints-swap-two-elements
            ( pr2 t)
            ( pair x p)
            ( eq-pair-Σ
              ( is-injective-inl (inv (pr1 (pair-eq-Σ eq))))
              ( eq-is-prop (is-prop-type-decidable-Prop (pr1 t x))))))
correct-Fin-succ-Fin-transposition n t (inl x) | inr np = refl
correct-Fin-succ-Fin-transposition n t (inr star) = refl

correct-Fin-succ-Fin-transposition-list : (n : ℕ) →
  (l : list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P → has-cardinality (Σ (Fin n) (λ x → type-decidable-Prop (P x))) 2))) →
  htpy-equiv
    ( permutation-list-transpositions (Fin (succ-ℕ n)) (map-list (Fin-succ-Fin-transposition n) l))
    ( pr1
      ( map-equiv
        ( extend-permutation-Fin-n n)
        ( permutation-list-transpositions (Fin n) l))) 
correct-Fin-succ-Fin-transposition-list n nil = inv-htpy (id-map-coprod (Fin n) unit)
correct-Fin-succ-Fin-transposition-list n (cons t l) x =
  correct-Fin-succ-Fin-transposition
    ( n)
    ( t)
    ( map-equiv (permutation-list-transpositions (Fin (succ-ℕ n)) (map-list (Fin-succ-Fin-transposition n) l)) x) ∙
      ( (ap
        ( map-equiv (pr1 (map-equiv (extend-permutation-Fin-n n) (transposition (Fin n) (pr1 t) (pr2 t)))))
        ( correct-Fin-succ-Fin-transposition-list n l x)) ∙
        ( inv
          ( comp-extend-permutation-Fin-n
            ( n)
            ( transposition (Fin n) (pr1 t) (pr2 t))
            ( permutation-list-transpositions (Fin n) l)
            ( x))))

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
        ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
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

retr-permutation-list-transpositions-Fin' : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
  (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
  (y z : Fin (succ-ℕ n)) → Id (map-equiv f y) z →
  Id
    ( map-equiv (permutation-list-transpositions (Fin (succ-ℕ n)) (list-transpositions-permutation-Fin (succ-ℕ n) f)) y)
    ( map-equiv f y)
retr-permutation-list-transpositions-Fin' zero-ℕ f (inr star) p (inr star) z q = inv p
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inl z) q =
  ap 
    (λ w →
      map-equiv
        ( permutation-list-transpositions
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
      ( inl y)) {y = pair (inl x) p}
    ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
    ( ap
      ( map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t)))
      ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
        ( inl y)) ∙
      (ap
        ( λ g →
          map-equiv
            ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))
            ( map-equiv
              ( pr1 (map-equiv (extend-permutation-Fin-n (succ-ℕ n)) g))
              ( inl y)))
        { x =
          permutation-list-transpositions ( Fin (succ-ℕ n)) (list-transpositions-permutation-Fin (succ-ℕ n) _)}
        { y = F'} 
        ( eq-htpy-equiv
          ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
          ( (ap (map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))) lemma) ∙
            (lemma2 ∙ inv q))))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x))) 2))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
  P = pair
    ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
    ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
      right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl)
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' = map-inv-equiv (extend-permutation-Fin-n (succ-ℕ n)) P
  lemma2 : Id
    (map-equiv
     (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t)) (inl z))
    (inl z)
  lemma2 = not-computation-transposition-two-elements
          ( has-decidable-equality-Fin)
          ( inr star)
          ( inl x)
          ( inl z)
          ( neq-inr-inl)
          ( neq-inr-inl)
          ( λ r →
            neq-inr-inl
              ( map-inv-equiv
                ( pair
                  ( ap (map-equiv f))
                  ( is-emb-is-equiv (pr2 f) (inr star) (inl y)))
                (p ∙ (r ∙ inv q))))
  lemma : Id (map-equiv (pr1 (map-equiv (extend-permutation-Fin-n (succ-ℕ n)) F')) (inl y)) (inl z)
  lemma =
    ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-permutation-Fin-n (succ-ℕ n)))) ∙
      ( ap (map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))) q ∙ lemma2)
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inr star) q =
  ap 
    (λ w →
      map-equiv
        ( permutation-list-transpositions
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
      ( inl y)) {y = pair (inl x) p}
    ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
    ( ap
      ( map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t)))
      ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
        ( inl y)) ∙
      (ap
        ( λ g →
          map-equiv
            ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))
            ( map-equiv
              ( pr1 (map-equiv (extend-permutation-Fin-n (succ-ℕ n)) g))
              ( inl y)))
        { x =
          permutation-list-transpositions ( Fin (succ-ℕ n)) (list-transpositions-permutation-Fin (succ-ℕ n) _)}
        { y = F'} 
        ( eq-htpy-equiv
          ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
        ( (ap (map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))) lemma) ∙
          ( (right-computation-transposition-two-elements
            ( has-decidable-equality-Fin)
            ( inr star)
            ( inl x)
            ( neq-inr-inl)) ∙
            ( inv q)))))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x))) 2))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
  P = pair
    ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
    ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
      right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl)
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' = map-inv-equiv (extend-permutation-Fin-n (succ-ℕ n)) P
  lemma : Id (map-equiv (pr1 (map-equiv (extend-permutation-Fin-n (succ-ℕ n)) F')) (inl y)) (inl x)
  lemma =
    ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-permutation-Fin-n (succ-ℕ n)))) ∙
      ( ap (map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t))) q ∙
        ( left-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl))
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inr star) z q =
  ap 
    (λ w →
      map-equiv
        ( permutation-list-transpositions
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
      ( inr star)) {y = pair (inl x) p}
    ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
    ( ap
      ( map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t)))
      ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
        ( inr star)) ∙
      ( ap
        ( map-equiv (transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t)))
        ( pr2 (map-equiv (extend-permutation-Fin-n (succ-ℕ n)) F')) ∙
        ( left-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl ∙
          inv p)))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P → has-cardinality (Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x))) 2))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' =
    map-inv-equiv
      ( extend-permutation-Fin-n (succ-ℕ n))
      ( pair
        ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
        ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
          right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl))
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inl z) q =
  ap 
    (λ w →
      map-equiv
        ( permutation-list-transpositions
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
      ( inl y)) {y = pair (inr star) p}
    ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inr star)))) ∙
    ( ( correct-Fin-succ-Fin-transposition-list
      ( succ-ℕ n)
      ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
      ( inl y)) ∙
      ( ( ap inl (retr-permutation-list-transpositions-Fin' n f' (map-equiv f' (inr star)) refl y (map-equiv f' y) refl)) ∙
        ( computation-inv-extend-permutation-Fin-n (succ-ℕ n) f p y)))
  where
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' = map-inv-equiv (extend-permutation-Fin-n (succ-ℕ n)) (pair f p)
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inr star) q =
  ex-falso
    ( neq-inr-inl
      ( map-inv-equiv
        ( pair (ap (map-equiv f)) (is-emb-is-equiv (pr2 f) (inr star) (inl y)))
        ( p ∙ inv q)))
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inr star) z q =
  ap 
    (λ w →
      map-equiv
        ( permutation-list-transpositions
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
      ( inr star)) {y = pair (inr star) p}
    ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inr star)))) ∙
    ( ( correct-Fin-succ-Fin-transposition-list
      ( succ-ℕ n)
      ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
      ( inr star)) ∙
      ( inv p))
  where
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' = map-inv-equiv (extend-permutation-Fin-n (succ-ℕ n)) (pair f p)

retr-permutation-list-transpositions-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
  htpy-equiv (permutation-list-transpositions (Fin n) (list-transpositions-permutation-Fin n f)) f
retr-permutation-list-transpositions-Fin zero-ℕ f ()
retr-permutation-list-transpositions-Fin (succ-ℕ n) f y =
  retr-permutation-list-transpositions-Fin' n f (map-equiv f (inr star)) refl y (map-equiv f y) refl
  
```
