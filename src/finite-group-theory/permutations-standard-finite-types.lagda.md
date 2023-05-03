# Permutations

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module finite-group-theory.permutations-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.orbits-permutations
open import finite-group-theory.transpositions

open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.iterating-involutions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.subgroups-generated-by-subsets-groups
open import group-theory.symmetric-groups

open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A permutation of `Fin n` is an automorphism of `Fin n`.

## Definitions

```agda
Permutation : (n : ℕ) → UU lzero
Permutation n = Aut (Fin n)
```

## Properties

### Every permutation on `Fin n` can be described as a composite of transpositions

```agda
list-transpositions-permutation-Fin' :
  (n : ℕ) (f : Permutation (succ-ℕ n)) →
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
  t = standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
      { inr star}
      { inl x}
      ( neq-inr-inl)
  f' : (Permutation (succ-ℕ n))
  f' =
    map-inv-equiv
      ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
      ( pair
        ( transposition t ∘e f)
        ( ( ap (λ y → map-transposition t y) p) ∙
          ( right-computation-standard-transposition
            ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
            { inr star}
            { inl x}
            ( neq-inr-inl))))
list-transpositions-permutation-Fin' (succ-ℕ n) f (inr star) p =
  map-list
    ( Fin-succ-Fin-transposition (succ-ℕ n))
    ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
  where
  f' : (Permutation (succ-ℕ n))
  f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

list-transpositions-permutation-Fin : (n : ℕ) → (f : Permutation n) →
  ( list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x))))))
list-transpositions-permutation-Fin zero-ℕ f = nil
list-transpositions-permutation-Fin (succ-ℕ n) f = list-transpositions-permutation-Fin' n f (map-equiv f (inr star)) refl

abstract
  retr-permutation-list-transpositions-Fin' : (n : ℕ) → (f : Permutation (succ-ℕ n)) →
    (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
    (y z : Fin (succ-ℕ n)) → Id (map-equiv f y) z →
    Id
      ( map-equiv (permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) f)) y)
      ( map-equiv f y)
  retr-permutation-list-transpositions-Fin' zero-ℕ f (inr star) p (inr star) z q = inv p
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inl z) q =
    ap
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inl y)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inl y)) ∙
        (ap
          ( λ g →
            map-equiv
              ( transposition t)
              ( map-equiv
                ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
                ( inl y)))
          { x =
            permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) _)}
          { y = F'}
          ( eq-htpy-equiv
            ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
            ( (ap (map-equiv (transposition t)) lemma) ∙
              (lemma2 ∙ inv q))))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t =
      standard-2-Element-Decidable-Subtype
        ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
        { inr star}
        { inl x}
        ( neq-inr-inl)
    P :
      Σ ( Permutation (succ-ℕ (succ-ℕ n)))
        ( λ g → Id (map-equiv g (inr star)) (inr star))
    P =
      pair
        ( transposition t ∘e f)
        ( ( ap (λ y → map-transposition t y) p) ∙
          ( right-computation-standard-transposition
            ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
            { inr star}
            { inl x}
            ( neq-inr-inl)))
    F' : (Permutation (succ-ℕ n))
    F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
    lemma2 : Id
      (map-equiv
      (transposition t) (inl z))
      (inl z)
    lemma2 =
      is-fixed-point-standard-transposition
        ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
        { inr star}
        { inl x}
        ( neq-inr-inl)
        ( inl z)
        ( neq-inr-inl)
        ( λ r →
          neq-inr-inl
            ( is-injective-map-equiv f (p ∙ (r ∙ inv q))))
    lemma :
      Id ( map-equiv
           ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F'))
           ( inl y))
         ( inl z)
    lemma =
      ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
        ( ap (map-equiv (transposition t)) q ∙ lemma2)
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inr star) q =
    ap
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inl y)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inl y)) ∙
        (ap
          ( λ g →
            map-equiv
              ( transposition t)
              ( map-equiv
                ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
                ( inl y)))
          { x =
            permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) _)}
          { y = F'}
          ( eq-htpy-equiv
            ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
          ( (ap (map-equiv (transposition t)) lemma) ∙
            ( (right-computation-standard-transposition
              ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
              { inr star}
              { inl x}
              ( neq-inr-inl)) ∙
              ( inv q)))))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t = standard-2-Element-Decidable-Subtype (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl
    P : Σ (Permutation (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
    P = pair
      ( transposition t ∘e f)
      ( ( ap (λ y → map-transposition t y) p) ∙
        right-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl)
    F' : (Permutation (succ-ℕ n))
    F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
    lemma : Id (map-equiv (pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) (inl y)) (inl x)
    lemma =
      ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
        ( ap (map-equiv (transposition t)) q ∙
          ( left-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl))
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inr star) z q =
    ap
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inr star)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inr star)) ∙
        ( ap
          ( map-equiv (transposition t))
          ( pr2 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) ∙
          ( left-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl ∙
            inv p)))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t = standard-2-Element-Decidable-Subtype (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl
    F' : (Permutation (succ-ℕ n))
    F' =
      map-inv-equiv
        ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
        ( pair
          ( transposition t ∘e f)
          ( ( ap (λ y → map-transposition t y) p) ∙
            right-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl))
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inl z) q =
    ap
      (λ w →
        map-equiv
          ( permutation-list-transpositions
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
    f' : (Permutation (succ-ℕ n))
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
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inr star)) {y = pair (inr star) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inr star)))) ∙
      ( ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
        ( inr star)) ∙
        ( inv p))
    where
    f' : (Permutation (succ-ℕ n))
    f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

  retr-permutation-list-transpositions-Fin : (n : ℕ) → (f : Permutation n) →
    htpy-equiv (permutation-list-transpositions (list-transpositions-permutation-Fin n f)) f
  retr-permutation-list-transpositions-Fin zero-ℕ f ()
  retr-permutation-list-transpositions-Fin (succ-ℕ n) f y =
    retr-permutation-list-transpositions-Fin' n f (map-equiv f (inr star)) refl y (map-equiv f y) refl
```
