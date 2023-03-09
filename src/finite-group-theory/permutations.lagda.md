# Permutations

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module finite-group-theory.permutations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.orbits-permutations
open import finite-group-theory.transpositions

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

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

### Every permutation on `Fin n` can be described as a composite of transpositions

```agda
list-transpositions-permutation-Fin' :
  (n : ℕ) (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
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
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
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

abstract
  retr-permutation-list-transpositions-Fin' : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
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
      Σ ( Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n)))
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
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
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
    P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
    P = pair
      ( transposition t ∘e f)
      ( ( ap (λ y → map-transposition t y) p) ∙
        right-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl)
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
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
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
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
    htpy-equiv (permutation-list-transpositions (list-transpositions-permutation-Fin n f)) f
  retr-permutation-list-transpositions-Fin zero-ℕ f ()
  retr-permutation-list-transpositions-Fin (succ-ℕ n) f y =
    retr-permutation-list-transpositions-Fin' n f (map-equiv f (inr star)) refl y (map-equiv f y) refl
```

### Every permutation of a type equipped with a counting can be described as a product of transpositions.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (eX : count X) (f : X ≃ X)
  where

  list-transpositions-permutation-count :
    list
      ( Σ
        ( X → decidable-Prop l2)
        ( λ P →
          has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))
  list-transpositions-permutation-count =
    map-list
      ( transposition-conjugation-equiv (Fin (number-of-elements-count eX)) X (equiv-count eX))
      ( list-transpositions-permutation-Fin (number-of-elements-count eX) ((inv-equiv-count eX ∘e f) ∘e equiv-count eX))

  abstract
    retr-permutation-list-transpositions-count :
      htpy-equiv (permutation-list-transpositions list-transpositions-permutation-count) f
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

### For `X` finite, the symmetric group of `X` is generated by transpositions

```agda
module _
  {l1 l2 : Level} (n : ℕ) (X : UU-Fin l1 n)
  where

  is-generated-transposition-symmetric-Fin-Level :
    is-generating-subset-Group
      ( symmetric-Group (set-UU-Fin n X))
      ( is-transposition-permutation-Prop)
  is-generated-transposition-symmetric-Fin-Level f =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin n X)
      ( subset-subgroup-subset-Group
        ( symmetric-Group (set-UU-Fin n X))
        ( is-transposition-permutation-Prop)
        ( f))
      ( λ h →
        unit-trunc-Prop
          ( pair
            ( map-list
              ( λ x → pair (inr star) (pair (transposition x) (unit-trunc-Prop (pair x refl))))
              ( list-transpositions-permutation-count (type-UU-Fin n X) (pair n h) f))
            ( ( lemma (list-transpositions-permutation-count (type-UU-Fin n X) (pair n h) f)) ∙
              ( eq-htpy-equiv (retr-permutation-list-transpositions-count (type-UU-Fin n X) (pair n h) f)))))
    where
    lemma : (l : list (2-Element-Decidable-Subtype l2 (type-UU-Fin n X))) →
      Id
        ( ev-formal-combination-subset-Group
          ( symmetric-Group (set-UU-Fin n X))
          ( is-transposition-permutation-Prop)
          ( map-list
            ( λ x →
              pair
                ( inr star)
                ( pair (transposition x) (unit-trunc-Prop (pair x refl))))
            ( l)))
        ( permutation-list-transpositions l)
    lemma nil = refl
    lemma (cons x l) = ap (λ g → (transposition x) ∘e g) (lemma l)
```

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  module _
    (f : (type-UU-Fin n X) ≃ (type-UU-Fin n X))
    where

    parity-transposition-permutation : UU (lsuc l)
    parity-transposition-permutation =
      Σ (Fin 2) (λ k →
        type-trunc-Prop
          (Σ
            ( list
              ( Σ ((type-UU-Fin n X) → decidable-Prop l)
                ( λ P → has-cardinality 2 (Σ (type-UU-Fin n X) (λ x → type-decidable-Prop (P x))))))
            ( λ li → Id k (mod-two-ℕ (length-list li)) × Id f (permutation-list-transpositions li))))

    abstract
      is-contr-parity-transposition-permutation : is-contr parity-transposition-permutation
      is-contr-parity-transposition-permutation =
        apply-universal-property-trunc-Prop
          ( has-cardinality-type-UU-Fin n X)
          ( is-trunc-Prop neg-two-𝕋 parity-transposition-permutation)
          ( λ h →
            pair
              ( pair
                ( mod-two-ℕ (length-list (list-transposition-f h)))
                ( unit-trunc-Prop
                  ( pair (list-transposition-f h)
                    ( pair refl
                      ( inv
                        ( eq-htpy-equiv (retr-permutation-list-transpositions-count (type-UU-Fin n X) (pair n h) f)))))))
              ( λ (pair k u) →
                eq-pair-Σ
                  ( apply-universal-property-trunc-Prop u
                    ( Id-Prop (Fin-Set 2) (mod-two-ℕ (length-list (list-transposition-f h))) k)
                    ( λ (pair li (pair q r)) →
                      is-injective-iterate-involution (mod-two-ℕ (length-list (list-transposition-f h))) k
                        ( sign-permutation-orbit n (pair (type-UU-Fin n X) (unit-trunc-Prop h)) id-equiv)
                        ( inv
                          ( iterate-involution (succ-Fin 2) (is-involution-aut-Fin-two-ℕ (equiv-succ-Fin 2))
                            (length-list (list-transposition-f h))
                            (sign-permutation-orbit n (pair (type-UU-Fin n X) (unit-trunc-Prop h)) id-equiv)) ∙
                          ( sign-list-transpositions-count (type-UU-Fin n X) (pair n h) (list-transposition-f h) ∙
                            ( ap
                              ( sign-permutation-orbit n (pair (type-UU-Fin n X) (unit-trunc-Prop h)))
                              { x = permutation-list-transpositions (list-transposition-f h)}
                              { y = permutation-list-transpositions li}
                              ( (eq-htpy-equiv (retr-permutation-list-transpositions-count
                                (type-UU-Fin n X) (pair n h) f)) ∙ r) ∙
                              ( inv (sign-list-transpositions-count (type-UU-Fin n X) (pair n h) li) ∙
                                ( (iterate-involution (succ-Fin 2) (is-involution-aut-Fin-two-ℕ (equiv-succ-Fin 2)) (length-list li)
                                  ( sign-permutation-orbit n (pair (type-UU-Fin n X) (unit-trunc-Prop h)) id-equiv)) ∙
                                  ( ap
                                    ( λ k → iterate (nat-Fin 2 k) (succ-Fin 2)
                                      ( sign-permutation-orbit n (pair (type-UU-Fin n X) (unit-trunc-Prop h)) id-equiv))
                                    ( inv q)))))))))
                  ( eq-is-prop is-prop-type-trunc-Prop)))
        where
        list-transposition-f : (h : Fin n ≃ (type-UU-Fin n X)) →
          list
            (Σ (type-UU-Fin n X → decidable-Prop l)
            (λ P → has-cardinality 2 (Σ (type-UU-Fin n X) (λ x → type-decidable-Prop (P x)))))
        list-transposition-f h = list-transpositions-permutation-count (type-UU-Fin n X) (pair n h) f
        is-injective-iterate-involution : (k k' x : Fin 2) →
          Id (iterate (nat-Fin 2 k) (succ-Fin 2) x) (iterate (nat-Fin 2 k') (succ-Fin 2) x) → Id k k'
        is-injective-iterate-involution (inl (inr star)) (inl (inr star)) x p = refl
        is-injective-iterate-involution (inl (inr star)) (inr star) (inl (inr star)) p = ex-falso (neq-inl-inr p)
        is-injective-iterate-involution (inl (inr star)) (inr star) (inr star) p = ex-falso (neq-inr-inl p)
        is-injective-iterate-involution (inr star) (inl (inr star)) (inl (inr star)) p = ex-falso (neq-inr-inl p)
        is-injective-iterate-involution (inr star) (inl (inr star)) (inr star) p = ex-falso (neq-inl-inr p)
        is-injective-iterate-involution (inr star) (inr star) x p = refl
```
