# Permutations

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.permutations where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)

open import finite-group-theory.transpositions using
  ( correct-Fin-succ-Fin-transposition-list; Fin-succ-Fin-transposition;
    left-computation-transposition-two-elements; map-transposition;
    not-computation-transposition-two-elements; permutation-list-transpositions;
    right-computation-transposition-two-elements; transposition; transposition-two-elements;
    transposition-conjugation-equiv; correct-transposition-conjugation-equiv-list)

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
  ( _≃_; _∘e_; eq-htpy-equiv; htpy-equiv; id-equiv; inv-equiv; is-emb-is-equiv; is-equiv;
    is-equiv-has-inverse; left-inverse-law-equiv; right-inverse-law-equiv; map-equiv; map-inv-equiv; htpy-eq-equiv)
open import foundation.equivalences-maybe using
  ( extend-equiv-Maybe; comp-extend-equiv-Maybe; computation-inv-extend-equiv-Maybe)
open import foundation.functions using (_∘_; id)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functoriality-coproduct-types using (id-map-coprod; map-coprod)
open import foundation.homotopies using (_~_; comp-htpy; refl-htpy; inv-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap)
open import foundation.involutions using (is-involution; is-equiv-is-involution)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.sets using (is-set-type-Set; Id-Prop)
open import foundation.type-arithmetic-empty-type using
  ( inv-right-unit-law-coprod-is-empty; map-right-absorption-prod)
open import foundation.unit-type using (star; unit)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.counting using
  ( count; equiv-count; inv-equiv-count; map-equiv-count; map-inv-equiv-count; number-of-elements-count)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin; Fin-Set)
open import univalent-combinatorics.finite-types using (has-cardinality)
open import univalent-combinatorics.lists using
  (cons; list; fold-list; map-list; nil)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Properties

### Every permutation of `Fin n` can be described as a product of transpositions for all `n : ℕ`.

```agda
list-transpositions-permutation-Fin' : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
  (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
  ( list
    ( Σ
      ( Fin (succ-ℕ n) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (P x))))))
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
    ( λ P →
      has-cardinality 2
        ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' =
    map-inv-equiv
      ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
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
  f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

list-transpositions-permutation-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
  ( list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x))))))
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
              ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
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
    ( λ P →
      has-cardinality 2
        ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
  P = pair
    ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
    ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
      right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl)
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
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
              ( is-injective-map-equiv f (p ∙ (r ∙ inv q))))
  lemma : Id (map-equiv (pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) (inl y)) (inl z)
  lemma =
    ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
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
              ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
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
    ( λ P →
      has-cardinality 2
        ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
  P = pair
    ( transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) ∘e f)
    ( ( ap (λ y → map-transposition (Fin (succ-ℕ (succ-ℕ n))) (pr1 t) (pr2 t) y) p) ∙
      right-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl)
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
  lemma : Id (map-equiv (pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) (inl y)) (inl x)
  lemma =
    ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
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
        ( pr2 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) ∙
        ( left-computation-transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl ∙
          inv p)))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P →
      has-cardinality 2
        ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
  t = transposition-two-elements has-decidable-equality-Fin (inr star) (inl x) neq-inr-inl 
  F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  F' =
    map-inv-equiv
      ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
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
        ( computation-inv-extend-equiv-Maybe (Fin-Set (succ-ℕ n)) f p y)))
  where
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)
retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inr star) q =
  ex-falso
    ( neq-inr-inl
      ( is-injective-map-equiv f (p ∙ inv q)))
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
  f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

retr-permutation-list-transpositions-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
  htpy-equiv (permutation-list-transpositions (Fin n) (list-transpositions-permutation-Fin n f)) f
retr-permutation-list-transpositions-Fin zero-ℕ f ()
retr-permutation-list-transpositions-Fin (succ-ℕ n) f y =
  retr-permutation-list-transpositions-Fin' n f (map-equiv f (inr star)) refl y (map-equiv f y) refl
```

### Every permutation of a type equipped with a counting can be described as a product of transpositions.

```agda
module _
  {l1 : Level} (X : UU l1) (eX : count X) (f : X ≃ X)
  where

  list-transpositions-permutation-count :
    list
      ( Σ
        ( X → decidable-Prop lzero)
        ( λ P →
          has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))
  list-transpositions-permutation-count =
    map-list
      ( transposition-conjugation-equiv (Fin (number-of-elements-count eX)) X (equiv-count eX))
      ( list-transpositions-permutation-Fin (number-of-elements-count eX) ((inv-equiv-count eX ∘e f) ∘e equiv-count eX))

  retr-permutation-list-transpositions-count :
    htpy-equiv (permutation-list-transpositions X list-transpositions-permutation-count) f
  retr-permutation-list-transpositions-count x =
    ( correct-transposition-conjugation-equiv-list
      ( Fin (number-of-elements-count eX))
      ( X)
      ( equiv-count eX)
      ( list-transpositions-permutation-Fin (number-of-elements-count eX) ((inv-equiv-count eX ∘e f) ∘e equiv-count eX))
      ( x)) ∙
      ( (ap
        ( map-equiv-count eX)
        ( retr-permutation-list-transpositions-Fin
          ( number-of-elements-count eX)
          ( (inv-equiv-count eX ∘e f) ∘e equiv-count eX)
          ( map-inv-equiv-count eX x))) ∙
        ( (htpy-eq-equiv (right-inverse-law-equiv (equiv-count eX)) (map-equiv ((f ∘e (equiv-count eX)) ∘e inv-equiv-count eX) x)) ∙
          ap (λ g → map-equiv (f ∘e g) x) (right-inverse-law-equiv (equiv-count eX))))
```
