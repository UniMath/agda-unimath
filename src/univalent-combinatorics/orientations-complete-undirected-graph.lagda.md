---
title: Orientations of the complete undirected graph
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.orientations-complete-undirected-graph where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-zero-ℕ'; trans-cong-ℕ; concatenate-cong-eq-ℕ; symm-cong-ℕ; scalar-invariant-cong-ℕ')
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; rewrite-left-add-dist-ℕ; symmetric-dist-ℕ)
open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; mod-two-ℕ; eq-mod-succ-cong-ℕ; add-Fin; ap-add-Fin; cong-add-Fin;
    dist-Fin; ap-dist-Fin; cong-dist-Fin; mul-Fin; ap-mul-Fin; left-zero-law-mul-Fin;
    is-zero-mod-succ-ℕ; cong-eq-mod-succ-ℕ; cong-add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using (mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import elementary-number-theory.equality-natural-numbers using (has-decidable-equality-ℕ)
open import elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( exists-not-not-forall-count)

open import finite-group-theory.transpositions using
  ( map-transposition; transposition; two-elements-transposition;
    left-computation-standard-transposition)

open import foundation.automorphisms using (Aut)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop;
    equiv-bool-decidable-Prop; prop-decidable-Prop)
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype; subtype-decidable-subtype;
    is-decidable-subtype; is-decidable-subtype-subtype-decidable-subtype;
    type-prop-decidable-subtype; is-prop-type-prop-decidable-subtype)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-equiv;
    is-decidable-neg; dn-elim-is-decidable; is-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( empty; ex-falso; equiv-is-empty; empty-Prop)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; inv-equiv; is-equiv-has-inverse; id-equiv; map-equiv; map-inv-equiv)
open import foundation.equivalence-classes using
  ( large-set-quotient; quotient-map-large-set-quotient; large-quotient-Set;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient')
open import foundation.equivalence-relations using (Eq-Rel; prop-Eq-Rel; type-Eq-Rel)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; ap; ap-binary; _∙_; tr)
open import foundation.injective-maps using
  ( is-injective; is-prop-is-injective; is-injective-map-equiv)
open import foundation.intersection using (intersection-decidable-subtype)
open import foundation.logical-equivalences using (equiv-iff)
open import foundation.mere-equivalences using (transitive-mere-equiv; mere-equiv)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop;
    trunc-Prop; type-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; is-prop; type-Prop; is-prop-function-type; eq-is-prop)
open import foundation.sets using (Id-Prop)
open import foundation.subtypes using (subtype; eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.universal-property-propositional-truncation-into-sets using
  (map-universal-property-set-quotient-trunc-Prop)
open import foundation.unit-type using (star)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; is-finite-2-Element-Decidable-Subtype;
    2-element-type-2-Element-Decidable-Subtype; precomp-equiv-2-Element-Decidable-Subtype;
    standard-2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-subtypes using
  ( type-prop-standard-2-Element-Subtype;
    is-prop-type-prop-standard-2-Element-Subtype;
    subtype-standard-2-Element-Subtype; type-standard-2-Element-Subtype;
    equiv-type-standard-2-Element-Subtype;
    has-two-elements-type-standard-2-Element-Subtype)
open import univalent-combinatorics.2-element-types using
  ( has-two-elements; 2-Element-Type; swap-2-Element-Type;
    map-swap-2-Element-Type; compute-swap-2-Element-Type;
    contradiction-3-distinct-element-2-Element-Type)
open import univalent-combinatorics.counting using (has-decidable-equality-count)
open import univalent-combinatorics.decidable-subtypes using (is-finite-decidable-subtype)
open import univalent-combinatorics.dependent-product-finite-types using (is-finite-Π)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin; has-decidable-equality-is-finite; is-set-is-finite)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( has-cardinality; UU-Fin-Level; type-UU-Fin-Level; mere-equiv-UU-Fin; is-finite; 
    equiv-has-cardinality-id-number-of-elements-is-finite; number-of-elements-is-finite;
    is-finite-type-UU-Fin-Level; is-finite-equiv; is-finite-Fin;
    number-of-elements-has-finite-cardinality; has-finite-cardinality-is-finite;
    all-elements-equal-has-finite-cardinality; has-finite-cardinality;
    is-finite-has-finite-cardinality; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; equiv-bool-Fin-two-ℕ; nat-Fin; is-zero-nat-zero-Fin)
open import univalent-combinatorics.symmetric-difference using
  (eq-symmetric-difference; symmetric-difference-decidable-subtype)

module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n)
  where

  orientation-Complete-Undirected-Graph : UU (lsuc l)
  orientation-Complete-Undirected-Graph = ((pair P H) : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
    Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x))

  orientation-Complete-Undirected-Graph-Aut :
    Aut (type-UU-Fin-Level X) → orientation-Complete-Undirected-Graph →
    orientation-Complete-Undirected-Graph
  pr1 (orientation-Complete-Undirected-Graph-Aut e d Y) =
    map-inv-equiv e (pr1 (d (precomp-equiv-2-Element-Decidable-Subtype e Y)))
  pr2 (orientation-Complete-Undirected-Graph-Aut e d Y) =
    pr2 (d (precomp-equiv-2-Element-Decidable-Subtype e Y))

  2-Element-Decidable-Subtype-subtype-pointwise-difference :
    orientation-Complete-Undirected-Graph → orientation-Complete-Undirected-Graph →
    2-Element-Decidable-Subtype l (type-UU-Fin-Level X) → decidable-Prop l
  pr1 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y) =
    ¬ (Id (d Y) (d' Y))
  pr1 (pr2 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)) =
    is-prop-neg
  pr2 (pr2 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)) =
    is-decidable-neg
      ( has-decidable-equality-is-finite
        ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
        ( d Y)
        ( d' Y))

  is-finite-subtype-pointwise-difference :
    (d d' : orientation-Complete-Undirected-Graph) →
    is-finite
      ( Σ
        ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
        ( λ Y → type-decidable-Prop (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)))
  is-finite-subtype-pointwise-difference d d' =
    is-finite-decidable-subtype
      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d d')
      ( is-finite-2-Element-Decidable-Subtype n X)

  mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    orientation-Complete-Undirected-Graph → orientation-Complete-Undirected-Graph → Fin 2
  mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d' =
    mod-two-ℕ (number-of-elements-is-finite (is-finite-subtype-pointwise-difference d d'))

{-
  eq-transposition-orientation-Complete-Undirected-Graph :
    (P : 2-Element-Decidable-Subtype l3 (type-UU-Fin-Level X)) →
    (d : orientation-Complete-Undirected-Graph) →
    Id
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        ( d)
        ( orientation-Complete-Undirected-Graph-Aut (transposition P) d))
      (inr star)
  eq-transposition-orientation-Complete-Undirected-Graph P d =
    {!!}
-}

  equiv-symmetric-difference-subtype-pointwise-difference :
    ( d1 d2 d3 : orientation-Complete-Undirected-Graph) →
    ( type-decidable-subtype
      ( symmetric-difference-decidable-subtype
        ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
        ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
        ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3)) ≃
      type-decidable-subtype
        ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3))
  equiv-symmetric-difference-subtype-pointwise-difference d1 d2 d3 =
    equiv-Σ
      ( λ x →
        pr1
          (subtype-decidable-subtype
            (2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3)
            ( x)))
      ( id-equiv)
      ( λ Y →
        equiv-iff
          ( prop-decidable-Prop
            ( symmetric-difference-decidable-subtype
              ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3)
              ( Y)))
          ( prop-decidable-Prop (2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3 Y))
          ( f Y)
          ( g Y))
    where
    f : (Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
      type-Prop
        ( prop-decidable-Prop
          ( symmetric-difference-decidable-subtype
            ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3) Y)) →
        type-Prop (prop-decidable-Prop (2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3 Y))
    f Y (inl (pair np nnq)) r =
      np (r ∙
        inv
          ( dn-elim-is-decidable
            ( Id (d2 Y) (d3 Y))
            ( has-decidable-equality-is-finite
              ( is-finite-decidable-subtype
                ( pr1 Y)
                ( is-finite-type-UU-Fin-Level X))
              ( d2 Y)
              ( d3 Y))
            ( nnq)))
    f Y (inr (pair nnp nq)) r =
      nq
        ( (inv
          ( dn-elim-is-decidable
            ( Id (d1 Y) (d2 Y))
            ( has-decidable-equality-is-finite
              ( is-finite-decidable-subtype
                ( pr1 Y)
                ( is-finite-type-UU-Fin-Level X))
              (d1 Y)
              (d2 Y))
            ( nnp))) ∙
        ( r))
    cases-g : (Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
      ¬ (Id (d1 Y) (d3 Y)) → (is-decidable (Id (d1 Y) (d2 Y))) →
      is-decidable (Id (d2 Y) (d3 Y)) →
      coprod
        (¬ (Id (d1 Y) (d2 Y)) × ¬ (¬ (Id (d2 Y) (d3 Y))))
        (¬ (¬ (Id (d1 Y) (d2 Y))) × ¬ (Id (d2 Y) (d3 Y)))
    cases-g Y nr (inl p) (inl q) = ex-falso (nr (p ∙ q))
    cases-g Y nr (inl p) (inr nq) = inr (pair (λ f → f p) nq)
    cases-g Y nr (inr np) (inl q) = inl (pair np (λ f → f q))
    cases-g Y nr (inr np) (inr nq) =
      ex-falso
        (apply-universal-property-trunc-Prop
          ( pr2 Y)
          ( empty-Prop)
          ( λ h →
            contradiction-3-distinct-element-2-Element-Type
              ( 2-element-type-2-Element-Decidable-Subtype Y)
              ( d1 Y)
              ( d2 Y)
              ( d3 Y)
              ( np)
              ( nq)
              ( nr)))
    g : (Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
      type-Prop
        ( prop-decidable-Prop
          ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3 Y)) →
        type-Prop
          ( prop-decidable-Prop
            ( symmetric-difference-decidable-subtype
              ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3) Y))
    g Y r =
      cases-g
        ( Y)
        ( r)
        ( has-decidable-equality-is-finite
          ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
          ( d1 Y)
          ( d2 Y))
        ( has-decidable-equality-is-finite
          ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
          ( d2 Y)
          ( d3 Y)) 

  even-difference-orientation-Complete-Undirected-Graph :
    Eq-Rel lzero orientation-Complete-Undirected-Graph
  pr1 even-difference-orientation-Complete-Undirected-Graph d d' =
    Id-Prop
      ( Fin-Set 2)
      ( zero-Fin)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d')
  pr1 (pr2 even-difference-orientation-Complete-Undirected-Graph) {d} =
    ap
      ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair 0 (unit-trunc-Prop (equiv-is-empty id (λ (pair _ np) → np refl))))
        ( has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d)))
  pr1 (pr2 (pr2 even-difference-orientation-Complete-Undirected-Graph)) {d} {d'} p =
    p ∙
      ap
        ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
        ( all-elements-equal-has-finite-cardinality
          ( has-finite-cardinality-d'-d)
          ( has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d' d)))
    where
    has-finite-cardinality-d'-d :
      has-finite-cardinality
        ( Σ
          ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
          ( λ Y → type-decidable-Prop (2-Element-Decidable-Subtype-subtype-pointwise-difference d' d Y)))
    pr1 has-finite-cardinality-d'-d =
      pr1 (has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d'))
    pr2 has-finite-cardinality-d'-d =
      apply-universal-property-trunc-Prop
        ( pr2 (has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d')))
        ( trunc-Prop
          ( Fin (pr1 has-finite-cardinality-d'-d) ≃
            ( Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d' Y) (d Y))))))
        ( λ h → unit-trunc-Prop (h' ∘e h))
      where
      h' :
        (Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d Y) (d' Y))) ≃
          Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d' Y) (d Y))))
      pr1 h' (pair Y np) = pair Y (λ p' → np (inv p'))
      pr2 h' =
        is-equiv-has-inverse
          ( λ (pair Y np) → pair Y (λ p' → np (inv p')))
          ( λ (pair Y np) → eq-pair-Σ refl (eq-is-prop is-prop-neg))
          ( λ (pair Y np) → eq-pair-Σ refl (eq-is-prop is-prop-neg))
  pr2 (pr2 (pr2 even-difference-orientation-Complete-Undirected-Graph)) {d1} {d2} {d3} p1 p2 =
    inv
      ( is-zero-mod-succ-ℕ
        ( 1)
        ( dist-ℕ (add-ℕ k1 k2) (mul-ℕ 2 k'))
        ( trans-cong-ℕ
          ( 2)
          ( add-ℕ k1 k2)
          ( zero-ℕ)
          ( mul-ℕ 2 k')
          ( concatenate-cong-eq-ℕ 2
            { x1 = add-ℕ k1 k2}
            ( symm-cong-ℕ 2
              ( add-ℕ
                ( nat-Fin
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2))
                ( nat-Fin
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d2 d3)))
              ( add-ℕ k1 k2)
              ( cong-add-ℕ k1 k2))
            ( ap-binary
              ( add-ℕ)
              ( ap nat-Fin (inv p1) ∙ is-zero-nat-zero-Fin {k = 2})
              ( ap nat-Fin (inv p2) ∙ is-zero-nat-zero-Fin {k = 2})))
          ( scalar-invariant-cong-ℕ' 2 0 2 k' (cong-zero-ℕ' 2)))) ∙
      (ap
        ( mod-two-ℕ)
        ( ( symmetric-dist-ℕ (add-ℕ k1 k2) (mul-ℕ 2 k')) ∙
          ( inv
            ( rewrite-left-add-dist-ℕ
              ( k)
              ( mul-ℕ 2 k')
              ( add-ℕ k1 k2)
              ( inv
                ( eq-symmetric-difference
                  ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
                  ( is-finite-2-Element-Decidable-Subtype n X)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3)))) ∙
            ( ap
              ( number-of-elements-has-finite-cardinality)
              ( all-elements-equal-has-finite-cardinality
                ( has-finite-cardinality-is-finite
                  ( is-finite-decidable-subtype
                    ( symmetric-difference-decidable-subtype
                      ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3))
                    ( is-finite-2-Element-Decidable-Subtype n X)))
               ( pair
                 ( number-of-elements-is-finite
                   ( is-finite-decidable-subtype
                     ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3)
                     ( is-finite-2-Element-Decidable-Subtype n X)))
                 ( transitive-mere-equiv
                   ( pr2
                    ( has-finite-cardinality-is-finite
                      ( is-finite-decidable-subtype
                        (2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3)
                        ( is-finite-2-Element-Decidable-Subtype n X))))
                   ( unit-trunc-Prop
                     ( inv-equiv
                       ( equiv-symmetric-difference-subtype-pointwise-difference d1 d2 d3))))))))))
    where
    k : ℕ
    k =
      number-of-elements-is-finite
        ( is-finite-decidable-subtype
          ( symmetric-difference-decidable-subtype
            ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3))
          ( is-finite-2-Element-Decidable-Subtype n X))
    k1 : ℕ
    k1 = number-of-elements-is-finite (is-finite-subtype-pointwise-difference d1 d2)
    k2 : ℕ
    k2 = number-of-elements-is-finite (is-finite-subtype-pointwise-difference d2 d3)
    k' : ℕ
    k' =
      number-of-elements-is-finite
        ( is-finite-decidable-subtype
          ( intersection-decidable-subtype
            ( 2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3))
          ( is-finite-2-Element-Decidable-Subtype n X))

  abstract
    is-decidable-even-difference-orientation-Complete-Undirected-Graph :
      (Y Y' : orientation-Complete-Undirected-Graph) →
      is-decidable
        (type-Eq-Rel even-difference-orientation-Complete-Undirected-Graph Y Y')
    is-decidable-even-difference-orientation-Complete-Undirected-Graph Y Y' =
      has-decidable-equality-is-finite
        ( is-finite-Fin)
        ( zero-Fin)
        ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph Y Y')

  quotient-sign : UU (lsuc l)
  quotient-sign = large-set-quotient even-difference-orientation-Complete-Undirected-Graph 

  module _
    (ineq : leq-ℕ 2 n)
    where

    private
      module _
        (h : Fin n ≃ type-UU-Fin-Level X)
        where

        i : type-UU-Fin-Level X
        i = map-equiv h (pr1 (two-distinct-elements-leq-2-Fin n ineq))
        j : type-UU-Fin-Level X
        j = map-equiv h (pr1 (pr2 (two-distinct-elements-leq-2-Fin n ineq)))
        np : ¬ (Id i j)
        np p =
          pr2
            ( pr2 (two-distinct-elements-leq-2-Fin n ineq))
            ( is-injective-map-equiv h p)
        cases-d1 : (Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
          ( two-elements : Σ (type-UU-Fin-Level X)
            ( λ x → Σ (type-UU-Fin-Level X)
              ( λ y → Σ (¬ (Id x y))
                ( λ np' →
                  Id
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count (pair n h))
                      ( np'))
                    ( Y))))) →
          is-decidable (Id (pr1 two-elements) i) →
          is-decidable (Id (pr1 two-elements) j) →
          is-decidable (Id (pr1 (pr2 two-elements)) i) →
          Σ (type-UU-Fin-Level X) (λ z → type-decidable-Prop (pr1 Y z))
        cases-d1 Y (pair x (pair y (pair np' P))) (inl q) r s =
          pair y (tr (λ Z → type-decidable-Prop (pr1 Z y)) P (inr refl))
        cases-d1 Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inl s) =
          pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))
        cases-d1 Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inr ns) =
          pair y (tr (λ Z → type-decidable-Prop (pr1 Z y)) P (inr refl))
        cases-d1 Y (pair x (pair y (pair np' P))) (inr nq) (inr nr) s = 
          pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))
        d1 : orientation-Complete-Undirected-Graph 
        d1 Y =
          cases-d1
            ( Y)
            ( two-elements-transposition (pair n h) Y)
            ( has-decidable-equality-count
              ( pair n h)
              ( pr1 (two-elements-transposition (pair n h) Y)) i)
            ( has-decidable-equality-count
              ( pair n h)
              ( pr1 (two-elements-transposition (pair n h) Y)) j)
            ( has-decidable-equality-count
              ( pair n h)
              ( pr1 (pr2 (two-elements-transposition (pair n h) Y))) i) 
        equiv-Fin-1-difference-d1-trans : Fin 1 ≃
          Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
          (λ Y →
            type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( d1)
                ( orientation-Complete-Undirected-Graph-Aut
                  ( transposition
                    (standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count (pair n h))
                      ( np)))
                  ( d1))
                ( Y)))
        pr1 (pr1 equiv-Fin-1-difference-d1-trans (inr star)) =
          standard-2-Element-Decidable-Subtype (has-decidable-equality-count (pair n h)) np
        pr2 (pr1 equiv-Fin-1-difference-d1-trans (inr star)) q =
          np
            ({!!} ∙ {!!})
            {-( is-injective-map-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count (pair n h))
                  ( np)))
              ( (left-computation-standard-transposition
                ( has-decidable-equality-count (pair n h))
                ( np)) ∙
                {!!}))-}
        pr2 equiv-Fin-1-difference-d1-trans =
          is-equiv-has-inverse
            ( λ x → inr star)
            ( λ T →
              retr-Fin-1-difference-d1-trans
                ( T)
                ( has-decidable-equality-is-finite
                  ( is-finite-2-Element-Decidable-Subtype
                    ( n)
                    ( X))
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count (pair n h))
                    ( np))
                  ( pr1 T)))
            ( sec-Fin-1-difference-d1-trans)
          where
          retr-Fin-1-difference-d1-trans :
            ( T :
              Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
                (λ Y →
                  type-decidable-Prop
                    (2-Element-Decidable-Subtype-subtype-pointwise-difference
                      ( d1)
                      ( orientation-Complete-Undirected-Graph-Aut
                        ( transposition
                          ( standard-2-Element-Decidable-Subtype
                            ( has-decidable-equality-count (pair n h))
                            ( np)))
                        {!!})
                      ( Y)))) →
            is-decidable
              ( Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count (pair n h))
                  ( np))
                ( pr1 T)) →
            Id (pr1 equiv-Fin-1-difference-d1-trans (inr star)) T
          retr-Fin-1-difference-d1-trans T (inl Q) =
            eq-pair-Σ
              ( Q)
              ( eq-is-prop
                ( is-prop-type-decidable-Prop
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                    ( d1)
                    ( orientation-Complete-Undirected-Graph-Aut
                      (transposition
                        (standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-count (pair n h))
                          ( np)))
                      ( d1))
                    ( pr1 T))))
          retr-Fin-1-difference-d1-trans T (inr NQ) =
            ex-falso {!!}
          sec-Fin-1-difference-d1-trans :
            ((λ x → inr {A = empty} star) ∘ pr1 equiv-Fin-1-difference-d1-trans) ~ id
          sec-Fin-1-difference-d1-trans (inr star) = refl
        lemma :
          Id
            1
            ( number-of-elements-is-finite
              ( is-finite-subtype-pointwise-difference
                ( d1)
                ( orientation-Complete-Undirected-Graph-Aut
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count (pair n h))
                      ( np)))
                  ( d1))))
        lemma =
          ap
            ( number-of-elements-has-finite-cardinality)
            ( all-elements-equal-has-finite-cardinality
              ( pair
                ( 1)
                ( unit-trunc-Prop equiv-Fin-1-difference-d1-trans))
              ( has-finite-cardinality-is-finite
                ( is-finite-subtype-pointwise-difference
                  ( d1)
                  ( orientation-Complete-Undirected-Graph-Aut
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count (pair n h))
                        ( np)))
                    ( d1)))))
        inv-orientation : (T : quotient-sign) →
          is-decidable
            ( type-class-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph)
              ( T)
              ( d1)) →
          Fin 2
        inv-orientation T (inl P) = inl (inr star)
        inv-orientation T (inr NP) = inr star
        equiv-Fin-2-count : Fin 2 ≃ quotient-sign
        pr1 equiv-Fin-2-count (inl (inr star)) =
          quotient-map-large-set-quotient
            even-difference-orientation-Complete-Undirected-Graph
            ( d1)
        pr1 equiv-Fin-2-count (inr star) =
          quotient-map-large-set-quotient
            even-difference-orientation-Complete-Undirected-Graph
            ( orientation-Complete-Undirected-Graph-Aut
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count (pair n h))
                  ( np)))
              ( d1))
        pr2 equiv-Fin-2-count =
          is-equiv-has-inverse
            ( λ T →
              inv-orientation
                ( T)
                ( is-decidable-type-class-large-set-quotient-is-decidable
                  ( even-difference-orientation-Complete-Undirected-Graph)
                  ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
                  ( T)
                  ( d1)))
            ( λ T →
              retr-orientation
               ( T)
               ( is-decidable-type-class-large-set-quotient-is-decidable
                 ( even-difference-orientation-Complete-Undirected-Graph)
                 ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
                 ( T)
                 ( d1)))
            {!!}
          where
          retr-orientation : (T : quotient-sign) →
            (H :
              is-decidable
                (type-class-large-set-quotient
                  ( even-difference-orientation-Complete-Undirected-Graph)
                  ( T)
                  ( d1))) →
            Id (pr1 equiv-Fin-2-count (inv-orientation T H)) T
          retr-orientation T (inl H) =
            eq-effective-quotient'
              ( even-difference-orientation-Complete-Undirected-Graph)
              ( d1)
              ( T)
              ( H)
          retr-orientation T (inr NH) =
            eq-effective-quotient'
              ( even-difference-orientation-Complete-Undirected-Graph)
              ( orientation-Complete-Undirected-Graph-Aut
                ( transposition
                  (standard-2-Element-Decidable-Subtype
                    (has-decidable-equality-count (pair n h))
                    ( np)))
                ( d1))
              ( T)
              {!!}

    mere-equiv-Fin-2-quotient-sign : (leq-ℕ 2 n) →
      mere-equiv (Fin 2) quotient-sign
    mere-equiv-Fin-2-quotient-sign ineq =
      apply-universal-property-trunc-Prop
        ( mere-equiv-UU-Fin-Level X)
        ( trunc-Prop (Fin 2 ≃ quotient-sign))
        ( λ h → unit-trunc-Prop (equiv-Fin-2-count h))
