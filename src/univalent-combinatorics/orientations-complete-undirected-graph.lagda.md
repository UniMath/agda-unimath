---
title: Orientations of the complete undirected graph
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --experimental-lossy-unification #-}

module univalent-combinatorics.orientations-complete-undirected-graph where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-zero-ℕ'; trans-cong-ℕ; concatenate-cong-eq-ℕ; concatenate-eq-cong-ℕ; symm-cong-ℕ; scalar-invariant-cong-ℕ')
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; rewrite-left-add-dist-ℕ; symmetric-dist-ℕ)
open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; mod-two-ℕ; eq-mod-succ-cong-ℕ; add-Fin; ap-add-Fin; cong-add-Fin;
    dist-Fin; ap-dist-Fin; cong-dist-Fin; mul-Fin; ap-mul-Fin; left-zero-law-mul-Fin;
    is-zero-mod-succ-ℕ; cong-eq-mod-succ-ℕ; cong-add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  (mul-ℕ; left-unit-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import elementary-number-theory.equality-natural-numbers using (has-decidable-equality-ℕ)
open import elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( exists-not-not-forall-count)

open import finite-group-theory.transpositions using
  ( map-transposition; transposition; two-elements-transposition;
    left-computation-standard-transposition;
    right-computation-standard-transposition;
    map-standard-transposition; standard-transposition;
    eq-transposition-precomp-standard-2-Element-Decidable-Subtype;
    eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype;
    is-fixed-point-standard-transposition; eq-two-elements-transposition;
    is-involution-map-transposition)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inl-inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop;
    type-decidable-Prop; equiv-bool-decidable-Prop; prop-decidable-Prop)
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype; subtype-decidable-subtype;
    is-decidable-subtype; is-decidable-subtype-subtype-decidable-subtype)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-equiv; is-decidable-neg;
    dn-elim-is-decidable; is-decidable-Prop; is-prop-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( empty; ex-falso; equiv-is-empty; empty-Prop)
open import foundation.equality-dependent-pair-types using
  (eq-pair-Σ; pair-eq-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; inv-equiv; is-equiv-has-inverse; id-equiv; map-equiv; map-inv-equiv;
    left-unit-law-equiv; right-unit-law-equiv; equiv-comp; is-equiv; right-inverse-law-equiv;
    left-inverse-law-equiv; eq-htpy-equiv; distributive-inv-comp-equiv)
open import foundation.equivalence-classes using
  ( large-set-quotient; quotient-map-large-set-quotient; large-quotient-Set;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient'; is-prop-type-class-large-set-quotient)
open import foundation.equivalence-relations using
  ( Eq-Rel; prop-Eq-Rel; type-Eq-Rel; trans-Eq-Rel; refl-Eq-Rel)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_; id)
open import foundation.function-extensionality using (htpy-eq; eq-htpy)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; ap; ap-binary; _∙_; tr)
open import foundation.injective-maps using
  ( is-injective; is-prop-is-injective; is-injective-map-equiv)
open import foundation.intersection using (intersection-decidable-subtype)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.logical-equivalences using (_↔_; equiv-iff)
open import foundation.mere-equivalences using (transitive-mere-equiv; mere-equiv)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop;
    trunc-Prop; type-trunc-Prop; all-elements-equal-type-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; is-prop; type-Prop; is-prop-function-type; eq-is-prop)
open import foundation.sets using (Id-Prop; UU-Set)
open import foundation.subtypes using (subtype; eq-subtype)
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.universal-property-propositional-truncation-into-sets using
  (map-universal-property-set-quotient-trunc-Prop)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; is-finite-2-Element-Decidable-Subtype;
    2-element-type-2-Element-Decidable-Subtype; precomp-equiv-2-Element-Decidable-Subtype;
    standard-2-Element-Decidable-Subtype; 2-element-type-standard-2-Element-Decidable-Subtype;
    is-commutative-standard-2-Element-Decidable-Subtype;
    preserves-comp-precomp-equiv-2-Element-Decidable-Subtype;
    eq-equal-elements-standard-2-Element-Decidable-Subtype)
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
open import univalent-combinatorics.counting using
  ( has-decidable-equality-count; count; number-of-elements-count;
    map-equiv-count; equiv-count; is-set-count)
open import univalent-combinatorics.decidable-subtypes using (is-finite-decidable-subtype)
open import univalent-combinatorics.dependent-function-types using (is-finite-Π)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin; has-decidable-equality-is-finite; is-set-is-finite)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( has-cardinality; UU-Fin-Level; type-UU-Fin-Level; has-cardinality-type-UU-Fin; is-finite; 
    equiv-has-cardinality-id-number-of-elements-is-finite; number-of-elements-is-finite;
    is-finite-type-UU-Fin-Level; is-finite-equiv; is-finite-Fin;
    number-of-elements-has-finite-cardinality; has-finite-cardinality-is-finite;
    all-elements-equal-has-finite-cardinality; has-finite-cardinality;
    is-finite-has-finite-cardinality; has-cardinality-type-UU-Fin-Level)
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

  abstract
    equiv-symmetric-difference-subtype-pointwise-difference :
      ( d1 d2 d3 : orientation-Complete-Undirected-Graph) →
      ( type-decidable-subtype
        ( symmetric-difference-decidable-subtype
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
      f Y (inr (pair nq nnp)) r =
        nq
          ( ( inv
              ( dn-elim-is-decidable
                ( Id (d1 Y) (d2 Y))
                ( has-decidable-equality-is-finite
                  ( is-finite-decidable-subtype
                    ( pr1 Y)
                    ( is-finite-type-UU-Fin-Level X))
                  ( d1 Y)
                  ( d2 Y))
                ( nnp))) ∙
            ( r))
      cases-g : (Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
        ¬ (Id (d1 Y) (d3 Y)) → (is-decidable (Id (d1 Y) (d2 Y))) →
        is-decidable (Id (d2 Y) (d3 Y)) →
        coprod
          (¬ (Id (d1 Y) (d2 Y)) × ¬ (¬ (Id (d2 Y) (d3 Y))))
          (¬ (Id (d2 Y) (d3 Y)) × ¬ (¬ (Id (d1 Y) (d2 Y))))
      cases-g Y nr (inl p) (inl q) = ex-falso (nr (p ∙ q))
      cases-g Y nr (inl p) (inr nq) = inr (pair nq (λ f → f p))
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
        type-decidable-Prop
          ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3 Y) →
        type-decidable-Prop
          ( symmetric-difference-decidable-subtype
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3) Y)
      g Y r =
        cases-g Y r
          ( has-decidable-equality-is-finite
            ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
            ( d1 Y)
            ( d2 Y))
          ( has-decidable-equality-is-finite
            ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
            ( d2 Y)
            ( d3 Y)) 
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    ( d d' : orientation-Complete-Undirected-Graph) (m : Fin 2) →
      Id m (mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d') →
      Id m (mod-two-number-of-differences-orientation-Complete-Undirected-Graph d' d)
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d' m p =
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

  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    (d1 d2 d3 : orientation-Complete-Undirected-Graph) ( m : Fin 2) →
    Id m (mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2) →
    Id m (mod-two-number-of-differences-orientation-Complete-Undirected-Graph d2 d3) →
    Id zero-Fin (mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d3)
  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2 d3 m p1 p2 =
    inv
      ( is-zero-mod-succ-ℕ
        ( 1)
        ( dist-ℕ (add-ℕ k1 k2) (mul-ℕ 2 k'))
        ( trans-cong-ℕ
          ( 2)
          ( add-ℕ k1 k2)
          ( zero-ℕ)
          ( mul-ℕ 2 k')
          ( trans-cong-ℕ 2
            ( add-ℕ k1 k2)
            ( add-ℕ
              ( nat-Fin
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2))
              ( nat-Fin
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d2 d3)))
            ( zero-ℕ)
            ( symm-cong-ℕ 2
              ( add-ℕ
                ( nat-Fin
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2))
                ( nat-Fin
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph d2 d3)))
              ( add-ℕ k1 k2)
              ( cong-add-ℕ k1 k2))
            ( concatenate-eq-cong-ℕ 2
              ( ( ap-binary
                ( add-ℕ)
                ( ap nat-Fin (inv p1))
                ( ap nat-Fin (inv p2))) ∙
                ( ap (λ n → add-ℕ n (nat-Fin m)) (inv (left-unit-law-mul-ℕ (nat-Fin m)))))
              ( scalar-invariant-cong-ℕ' 2 2 0 (nat-Fin m) (cong-zero-ℕ' 2))))
          ( scalar-invariant-cong-ℕ' 2 0 2 k' (cong-zero-ℕ' 2)))) ∙
      ( ap
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
    is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d' zero-Fin p  
  pr2 (pr2 (pr2 even-difference-orientation-Complete-Undirected-Graph)) {d1} {d2} {d3} p1 p2 =
    eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph d1 d2 d3 zero-Fin p1 p2

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
  
  quotient-sign-Set : UU-Set (lsuc l)
  quotient-sign-Set = large-quotient-Set even-difference-orientation-Complete-Undirected-Graph

module _
  {l : Level} (n : ℕ)
  where

  map-orientation-complete-undirected-graph-equiv : (X X' : UU-Fin-Level l n) →
    (type-UU-Fin-Level X ≃ type-UU-Fin-Level X') → orientation-Complete-Undirected-Graph n X' →
    orientation-Complete-Undirected-Graph n X
  pr1 (map-orientation-complete-undirected-graph-equiv X X' e d Y) =
    map-inv-equiv e (pr1 (d (precomp-equiv-2-Element-Decidable-Subtype e Y)))
  pr2 (map-orientation-complete-undirected-graph-equiv X X' e d Y) =
    pr2 (d (precomp-equiv-2-Element-Decidable-Subtype e Y))

  orientation-complete-undirected-graph-equiv : (X X' : UU-Fin-Level l n) →
    (type-UU-Fin-Level X ≃ type-UU-Fin-Level X') →
    orientation-Complete-Undirected-Graph n X' ≃ orientation-Complete-Undirected-Graph n X
  pr1 (orientation-complete-undirected-graph-equiv X X' e) =
    map-orientation-complete-undirected-graph-equiv X X' e
  pr2 (orientation-complete-undirected-graph-equiv X X' e) =
    is-equiv-has-inverse
      ( map-orientation-complete-undirected-graph-equiv X' X (inv-equiv e))
      ( λ d →
        eq-htpy
          ( λ Y →
            eq-pair-Σ
              ( ( ap
                ( λ Y' → (map-inv-equiv e ∘ (map-inv-equiv (inv-equiv e))) (pr1 (d Y')))
                ( eq-pair-Σ
                  ( ap
                    ( λ h → pr1 Y ∘ map-equiv h)
                    ( right-inverse-law-equiv (inv-equiv e)) )
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( ap (λ h → map-equiv h (pr1 (d Y))) (right-inverse-law-equiv (inv-equiv e))))
              ( eq-is-prop (is-prop-type-decidable-Prop (pr1 Y (pr1 (id d Y)))))))
      ( λ d →
        eq-htpy
          ( λ Y →
            eq-pair-Σ
              ( ( ap
                ( λ Y' → (map-inv-equiv (inv-equiv e) ∘ map-inv-equiv e) (pr1 (d Y')))
                ( eq-pair-Σ
                  ( ap
                    ( λ h → pr1 Y ∘ map-equiv h)
                    ( left-inverse-law-equiv (inv-equiv e)) )
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( ap (λ h → map-equiv h (pr1 (d Y))) (left-inverse-law-equiv (inv-equiv e))))
              ( eq-is-prop (is-prop-type-decidable-Prop (pr1 Y (pr1 (id d Y)))))))

  abstract
    preserves-id-equiv-orientation-complete-undirected-graph-equiv :
      (X : UU-Fin-Level l n) →
      Id (orientation-complete-undirected-graph-equiv X X id-equiv) id-equiv
    preserves-id-equiv-orientation-complete-undirected-graph-equiv X =
      eq-htpy-equiv
        ( λ d →
          eq-htpy
            ( λ Y →
              eq-pair-Σ
                ( ap (λ Y' → pr1 (d Y')) (eq-pair-Σ refl (eq-is-prop is-prop-type-trunc-Prop)))
                ( eq-is-prop (is-prop-type-decidable-Prop (pr1 Y (pr1 (map-equiv id-equiv d Y)))))))

    preserves-comp-orientation-complete-undirected-graph-equiv :
      ( X Y Z : UU-Fin-Level l n) (e : type-UU-Fin-Level X ≃ type-UU-Fin-Level Y) →
      ( f : type-UU-Fin-Level Y ≃ type-UU-Fin-Level Z) →
      Id
        ( orientation-complete-undirected-graph-equiv X Z (f ∘e e))
        ( ( orientation-complete-undirected-graph-equiv X Y e) ∘e
          ( orientation-complete-undirected-graph-equiv Y Z f))
    preserves-comp-orientation-complete-undirected-graph-equiv X Y Z e f =
      eq-htpy-equiv
        ( λ d →
          eq-htpy
            ( λ S →
              eq-pair-Σ
                ( ( ap
                  ( λ S' → map-inv-equiv (f ∘e e) (pr1 (d S')))
                  ( htpy-eq
                    ( preserves-comp-precomp-equiv-2-Element-Decidable-Subtype e f)
                    ( S))) ∙
                  ( ap
                    ( λ g →
                      map-equiv
                        ( g)
                        ( pr1
                          ( d
                            ( ( precomp-equiv-2-Element-Decidable-Subtype f ∘
                              precomp-equiv-2-Element-Decidable-Subtype e)
                            ( S)))))
                    ( distributive-inv-comp-equiv e f)))
                ( eq-is-prop
                  ( is-prop-type-decidable-Prop
                    ( pr1 S
                      ( pr1
                        ( map-equiv
                          ( orientation-complete-undirected-graph-equiv X Y e ∘e
                            orientation-complete-undirected-graph-equiv Y Z f)
                          ( d)
                          ( S))))))))

    preserves-even-difference-orientation-complete-undirected-graph-equiv :
      (X X' : UU-Fin-Level l n) ( e : type-UU-Fin-Level X ≃ type-UU-Fin-Level X') →
      ( d d' : orientation-Complete-Undirected-Graph n X') →
      ( type-Eq-Rel (even-difference-orientation-Complete-Undirected-Graph n X') d d' ↔
        type-Eq-Rel
          ( even-difference-orientation-Complete-Undirected-Graph n X)
          ( map-orientation-complete-undirected-graph-equiv X X' e d)
          ( map-orientation-complete-undirected-graph-equiv X X' e d'))
    pr1 (preserves-even-difference-orientation-complete-undirected-graph-equiv X X' e d d') P =
      ( P) ∙
        ( ap
          ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
          ( all-elements-equal-has-finite-cardinality
            ( has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference n X' d d'))
            ( pair
              ( number-of-elements-is-finite
                ( is-finite-subtype-pointwise-difference n X
                  ( map-orientation-complete-undirected-graph-equiv X X' e d)
                  ( map-orientation-complete-undirected-graph-equiv X X' e d')))
              ( map-trunc-Prop
                ( λ h → equiv-subtype-pointwise-difference-equiv ∘e h)
                ( pr2
                  ( has-finite-cardinality-is-finite
                    ( is-finite-subtype-pointwise-difference n X
                      ( map-orientation-complete-undirected-graph-equiv X X' e d)
                      ( map-orientation-complete-undirected-graph-equiv X X' e d'))))))))
      where
      equiv-subtype-pointwise-difference-equiv :
        Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X))
          ( λ Y →
            type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference n X
                ( map-orientation-complete-undirected-graph-equiv X X' e d)
                ( map-orientation-complete-undirected-graph-equiv X X' e d')
                ( Y))) ≃
        Σ (2-Element-Decidable-Subtype l (type-UU-Fin-Level X'))
          ( λ Y →
            type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference n X' d d' Y))
      pr1 (pr1 equiv-subtype-pointwise-difference-equiv (pair Y NQ)) = precomp-equiv-2-Element-Decidable-Subtype e Y
      pr2 (pr1 equiv-subtype-pointwise-difference-equiv (pair Y NQ)) p =
        NQ
          ( eq-pair-Σ
            ( ap (map-inv-equiv e) (pr1 (pair-eq-Σ p)))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( pr1 Y (pr1 (map-orientation-complete-undirected-graph-equiv X X' e d' Y))))))
      pr2 equiv-subtype-pointwise-difference-equiv =
        is-equiv-has-inverse
          ( λ (pair Y NQ) →
            pair
              ( precomp-equiv-2-Element-Decidable-Subtype (inv-equiv e) Y)
              ( λ p →
                NQ
                  ( eq-pair-Σ
                    ( ( ap
                      ( λ Y' → pr1 (d Y'))
                      ( eq-pair-Σ
                        ( ap
                          ( λ h → pr1 Y ∘ (map-equiv h))
                          ( inv (right-inverse-law-equiv e)))
                        ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( ( is-injective-map-equiv (inv-equiv e) (pr1 (pair-eq-Σ p))) ∙
                        ( ap
                          ( λ Y' → pr1 (d' Y'))
                          ( eq-pair-Σ
                            ( ap
                              ( λ h → pr1 Y ∘ map-equiv h)
                              ( right-inverse-law-equiv e))
                            ( eq-is-prop is-prop-type-trunc-Prop)))))
                    ( eq-is-prop (is-prop-type-decidable-Prop (pr1 Y (pr1 (d' Y))))))))
          ( λ (pair Y NQ) →
            eq-pair-Σ
              ( eq-pair-Σ
                ( ap (λ h → pr1 Y ∘ map-equiv h) (right-inverse-law-equiv e))
                ( eq-is-prop is-prop-type-trunc-Prop))
              ( eq-is-prop
                ( is-prop-type-decidable-Prop
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference n X' d d' Y))))
          ( λ (pair Y NQ) →
            eq-pair-Σ
              ( eq-pair-Σ
                ( ap (λ h → pr1 Y ∘ map-equiv h) (left-inverse-law-equiv e))
                ( eq-is-prop is-prop-type-trunc-Prop))
              ( eq-is-prop
                ( is-prop-type-decidable-Prop
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference n X
                    ( map-orientation-complete-undirected-graph-equiv X X' e d)
                    ( map-orientation-complete-undirected-graph-equiv X X' e d')
                    ( Y)))))
    pr2 (preserves-even-difference-orientation-complete-undirected-graph-equiv X X' e d d') P =
      tr
        ( λ g →
          type-Eq-Rel
            ( even-difference-orientation-Complete-Undirected-Graph n X')
            ( map-equiv g d)
            ( map-equiv g d'))
        { x =
          orientation-complete-undirected-graph-equiv X' X (inv-equiv e) ∘e
          orientation-complete-undirected-graph-equiv X X' e}
        { y = id-equiv}
        ( inv (preserves-comp-orientation-complete-undirected-graph-equiv X' X X' (inv-equiv e) e) ∙
          ( ( ap (orientation-complete-undirected-graph-equiv X' X') (right-inverse-law-equiv e)) ∙
            ( preserves-id-equiv-orientation-complete-undirected-graph-equiv X')))
        ( pr1
          ( preserves-even-difference-orientation-complete-undirected-graph-equiv
            ( X')
            ( X)
            ( inv-equiv e)
            ( map-orientation-complete-undirected-graph-equiv X X' e d)
            ( map-orientation-complete-undirected-graph-equiv X X' e d'))
          ( P))
```

```agda
module _
  {l : Level} {X : UU l} (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  cases-orientation-aut-count : (e : X ≃ X) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (¬ (Id x y))
          ( λ np →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))
              ( Y))))) →
    is-decidable (Id (map-equiv e (pr1 two-elements)) (pr1 two-elements)) →
    is-decidable (Id (map-equiv e (pr1 (pr2 two-elements))) (pr1 (pr2 two-elements))) →
    Σ X (λ z → type-decidable-Prop (pr1 Y z))
  cases-orientation-aut-count e Y (pair x (pair y (pair np P))) (inl q) r =
    pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))
  cases-orientation-aut-count e Y (pair x (pair y (pair np P))) (inr nq) (inl nr) =
    pair y (tr (λ Z → type-decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-aut-count e Y (pair x (pair y (pair np P))) (inr nq) (inr nr) =
    pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))
 
  orientation-aut-count : X ≃ X →
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  orientation-aut-count e Y =
    cases-orientation-aut-count e Y
      ( two-elements-transposition eX Y)
      ( has-decidable-equality-count eX
        ( map-equiv e (pr1 (two-elements-transposition eX Y)))
        ( pr1 (two-elements-transposition eX Y)))
      ( has-decidable-equality-count eX
        ( map-equiv e (pr1 (pr2 (two-elements-transposition eX Y))))
        ( pr1 (pr2 (two-elements-transposition eX Y))))
    
  cases-orientation-two-elements-count : (i j : X)
    (Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (¬ (Id x y))
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    Σ X (λ z → type-decidable-Prop (pr1 Y z))
  cases-orientation-two-elements-count i j Y (pair x (pair y (pair np' P))) (inl q) r s =
    pair y (tr (λ Z → type-decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-two-elements-count i j Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inl s) =
    pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))
  cases-orientation-two-elements-count i j Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inr ns) =
    pair y (tr (λ Z → type-decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-two-elements-count i j Y (pair x (pair y (pair np' P))) (inr nq) (inr nr) s = 
    pair x (tr (λ Z → type-decidable-Prop (pr1 Z x)) P (inl refl))

  orientation-two-elements-count : (i j : X) → ¬ (Id i j) →
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  orientation-two-elements-count i j np Y =
    cases-orientation-two-elements-count i j Y
      ( two-elements-transposition eX Y)
      ( has-decidable-equality-count eX
        ( pr1 (two-elements-transposition eX Y)) i)
      ( has-decidable-equality-count eX
        ( pr1 (two-elements-transposition eX Y)) j)
      ( has-decidable-equality-count eX
        ( pr1 (pr2 (two-elements-transposition eX Y))) i) 

  first-element-count : X
  first-element-count =
    map-equiv-count
      ( eX)
      ( pr1
        ( two-distinct-elements-leq-2-Fin
          ( number-of-elements-count eX)
          ( ineq)))

  second-element-count : X
  second-element-count =
    map-equiv-count
      ( eX)
      ( pr1
        ( pr2
          ( two-distinct-elements-leq-2-Fin
            ( number-of-elements-count eX)
            ( ineq))))
          
  abstract
    distinct-two-elements-count : ¬ (Id first-element-count second-element-count)
    distinct-two-elements-count p =
      pr2
        ( pr2
          ( two-distinct-elements-leq-2-Fin
            ( number-of-elements-count eX)
            ( ineq)))
        ( is-injective-map-equiv (equiv-count eX) p)

  canonical-2-Element-Decidable-Subtype-count : 2-Element-Decidable-Subtype l X
  canonical-2-Element-Decidable-Subtype-count =
    standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-count eX)
      ( distinct-two-elements-count)

  canonical-orientation-count : 
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  canonical-orientation-count =
    orientation-two-elements-count first-element-count second-element-count distinct-two-elements-count

  trans-canonical-orientation-count : 
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  trans-canonical-orientation-count =
    orientation-two-elements-count
      ( second-element-count)
      ( first-element-count)
      ( λ p → distinct-two-elements-count (inv p))

  abstract
    cases-inward-edge-left-two-elements-orientation-count :
      (i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ¬ (Id x i) → ¬ (Id x j) →
      coprod
        ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i))
        ( ( Id (pr1 (two-elements-transposition eX Y)) i) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    cases-inward-edge-left-two-elements-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) =
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( two-elements-transposition eX Y)
              ( pr1 d)
              ( pr2 d)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)))
        { x =
          pair
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)}
        { y = pair (inr (λ p → nq (inv r1 ∙ p))) (inr (λ p → nr (inv r1 ∙ p)))}
        ( eq-pair-Σ
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
        ( r1)
    cases-inward-edge-left-two-elements-orientation-count
      i j np Y x nq nr (inr (pair r1 r2)) =
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( two-elements-transposition eX Y)
              ( d)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)))
        { x = ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)}
        { y = inl r1 }
        ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))) ∙
        ( r2)

    inward-edge-left-two-elements-orientation-count :
      ( i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-decidable-Prop (pr1 Y x)) → 
      ( type-decidable-Prop (pr1 Y i)) →
      ¬ (Id x i) → ¬ (Id x j) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-left-two-elements-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-left-two-elements-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x i nq p1 p2)

    cases-inward-edge-left-transposition-orientation-count :
      (i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ¬ (Id x i) → ¬ (Id x j) →
      coprod
        ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i))
        ( ( Id (pr1 (two-elements-transposition eX Y)) i) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    cases-inward-edge-left-transposition-orientation-count 
      i j np Y x nq nr (inl (pair r1 r2)) = 
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-aut-count
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( Y)
              ( two-elements-transposition eX Y)
              ( d)
              ( has-decidable-equality-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (pr2 (two-elements-transposition eX Y))))
                ( pr1 (pr2 (two-elements-transposition eX Y))))))
        { x =
          has-decidable-equality-count eX
            ( map-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( pr1 (two-elements-transposition eX Y)))
            ( pr1 (two-elements-transposition eX Y))}
          
        { y =
          inl
            ( tr
              ( λ y →
                Id
                  ( map-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( y))
                  ( y))
              ( inv r1)
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( x)
                ( λ q → nq (inv q))
                ( λ r → nr (inv r))))}
        ( eq-is-prop
          ( is-prop-is-decidable
            ( is-set-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (two-elements-transposition eX Y)))
              ( pr1 (two-elements-transposition eX Y)))))) ∙
        ( r1)
    cases-inward-edge-left-transposition-orientation-count 
      i j np Y x nq nr (inr (pair r1 r2)) =
      ( ap
        ( λ w →
          pr1
            ( cases-orientation-aut-count
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( Y)
              ( two-elements-transposition eX Y)
              ( pr1 w)
              ( pr2 w)))
        { x =
          pair
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (two-elements-transposition eX Y)))
              ( pr1 (two-elements-transposition eX Y)))
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (pr2 (two-elements-transposition eX Y))))
              ( pr1 (pr2 (two-elements-transposition eX Y))))}
        { y =
          pair
            ( inr
              ( λ s →
                np
                  ( inv r1 ∙
                    ( inv s ∙
                       tr
                        ( λ y →
                          Id
                            ( map-equiv
                              ( transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-count eX)
                                  ( np)))
                              ( y))
                            ( j))
                        ( inv r1)
                        ( left-computation-standard-transposition
                          ( has-decidable-equality-count eX)
                          ( np))))))
            ( inl
              ( tr
                ( λ y →
                  Id
                    ( map-equiv
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-count eX)
                          ( np)))
                      ( y))
                    ( y))
                ( inv r2)
                ( is-fixed-point-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np)
                  ( x)
                  ( λ q → nq (inv q))
                  ( λ r → nr (inv r)))))}
        ( eq-pair-Σ
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (two-elements-transposition eX Y)))
                ( pr1 (two-elements-transposition eX Y))))) 
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (pr2 (two-elements-transposition eX Y))))
                ( pr1 (pr2 (two-elements-transposition eX Y)))))))) ∙
        ( r2)

    inward-edge-left-transposition-orientation-count :
      ( i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-decidable-Prop (pr1 Y x)) → 
      ( type-decidable-Prop (pr1 Y i)) →
      ¬ (Id x i) → ¬ (Id x j) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))
            ( Y)))
        ( x)
    inward-edge-left-transposition-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-left-transposition-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x i nq p1 p2)

    cases-inward-edge-right-two-elements-orientation-count :
      (i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ¬ (Id x i) → ¬ (Id x j) →
      coprod
        ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j))
        ( ( Id (pr1 (two-elements-transposition eX Y)) j) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    cases-inward-edge-right-two-elements-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) = 
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( two-elements-transposition eX Y)
              ( pr1 d)
              ( pr2 d)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)))
        { x =
          pair
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)}
        { y = pair (inr (λ p → nq (inv r1 ∙ p))) (inr (λ p → nr (inv r1 ∙ p)))}
        ( eq-pair-Σ
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
        ( r1)
    cases-inward-edge-right-two-elements-orientation-count
      i j np Y x nq nr (inr (pair r1 r2)) =
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( two-elements-transposition eX Y)
              ( pr1 d)
              ( pr2 d)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)))
        { x =
          pair
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)}
        { y = pair (inr λ p → np (inv p ∙ r1)) (inl r1)}
        ( eq-pair-Σ
          ( eq-is-prop (is-prop-is-decidable ( is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
        ( ( ap
          ( λ d →
            pr1
              ( cases-orientation-two-elements-count i j Y
                ( two-elements-transposition eX Y)
                ( inr λ p → np (inv p ∙ r1))
                ( inl r1)
                ( d)))
          { x = has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i}
          { y = inr (λ q → nq (inv r2 ∙ q))}
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)))) ∙
          ( r2))

    inward-edge-right-two-elements-orientation-count :
      ( i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-decidable-Prop (pr1 Y x)) → 
      ( type-decidable-Prop (pr1 Y j)) →
      ¬ (Id x i) → ¬ (Id x j) →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-right-two-elements-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-right-two-elements-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x j nr p1 p2)

    cases-inward-edge-right-transposition-orientation-count :
      (i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ¬ (Id x i) → ¬ (Id x j) →
      coprod
        ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j))
        ( ( Id (pr1 (two-elements-transposition eX Y)) j) ×
          ( Id (pr1 (pr2 (two-elements-transposition eX Y))) x)) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    cases-inward-edge-right-transposition-orientation-count
      i j np Y x nq nr (inl (pair r1 r2)) =
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-aut-count
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( Y)
              ( two-elements-transposition eX Y)
              ( d)
              ( has-decidable-equality-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (pr2 (two-elements-transposition eX Y))))
                ( pr1 (pr2 (two-elements-transposition eX Y))))))
        { x =
          has-decidable-equality-count eX
            ( map-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( pr1 (two-elements-transposition eX Y)))
            ( pr1 (two-elements-transposition eX Y))}
        { y =
          inl
            ( tr
              ( λ y →
                Id
                  ( map-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( y))
                  ( y))
              ( inv r1)
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( x)
                ( λ q → nq (inv q))
                ( λ r → nr (inv r))))}
        ( eq-is-prop
          ( is-prop-is-decidable
            ( is-set-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (two-elements-transposition eX Y)))
              ( pr1 (two-elements-transposition eX Y)))))) ∙
        ( r1)
    cases-inward-edge-right-transposition-orientation-count
      i j np Y x nq nr (inr (pair r1 r2)) =
      ( ap
        ( λ w →
          pr1
            ( cases-orientation-aut-count
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( Y)
              ( two-elements-transposition eX Y)
              ( pr1 w)
              ( pr2 w)))
        { x =
          pair
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (two-elements-transposition eX Y)))
              ( pr1 (two-elements-transposition eX Y)))
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( pr1 (pr2 (two-elements-transposition eX Y))))
              ( pr1 (pr2 (two-elements-transposition eX Y))))}
        { y =
          pair
            ( inr
               λ s →
                np
                  ( ( tr
                    ( λ y →
                      Id
                        ( i)
                        ( map-equiv
                          ( transposition
                            ( standard-2-Element-Decidable-Subtype
                              ( has-decidable-equality-count eX)
                              ( np)))
                          ( y)))
                    ( inv r1)
                    ( inv
                      ( right-computation-standard-transposition
                        ( has-decidable-equality-count eX)
                        ( np))) ∙
                    ( s ∙ r1))))
            ( inl
              ( tr
                ( λ y →
                  Id
                    ( map-equiv
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-count eX)
                          ( np)))
                      ( y))
                    ( y))
                ( inv r2)
                ( is-fixed-point-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np)
                  ( x)
                  ( λ q → nq (inv q))
                  ( λ r → nr (inv r)))))}
        ( eq-pair-Σ
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (two-elements-transposition eX Y)))
                ( pr1 (two-elements-transposition eX Y)))))
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX
                ( map-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( pr1 (pr2 (two-elements-transposition eX Y))))
                ( pr1 (pr2 (two-elements-transposition eX Y)))))))) ∙
        ( r2)

    inward-edge-right-transposition-orientation-count :
      ( i j : X) (np : ¬ (Id i j)) ( Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-decidable-Prop (pr1 Y x)) → 
      ( type-decidable-Prop (pr1 Y j)) →
      ¬ (Id x i) → ¬ (Id x j) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    inward-edge-right-transposition-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-right-transposition-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x j nr p1 p2)

    cases-eq-orientation-two-elements-count : (i j : X) (np : ¬ (Id i j)) →
      ( two-elements : Σ X
        ( λ x → Σ X
          ( λ y → Σ (¬ (Id x y))
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np')
                ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))))) →
      (q : is-decidable (Id (pr1 two-elements) i)) →
      (r : is-decidable (Id (pr1 two-elements) j)) →
      (s : is-decidable (Id (pr1 (pr2 two-elements)) i)) →
      (t : is-decidable (Id (pr1 (pr2 two-elements)) j)) →
      Id
        ( pr1
          ( cases-orientation-two-elements-count i j
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))
            ( two-elements)
            ( q)
            ( r)
            ( s)))
        ( j)
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inl q) r s (inl t) = t
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inl q) r s (inr nt) =
      ex-falso
        ( nt
          ( ( inv
            ( left-computation-standard-transposition (has-decidable-equality-count eX) np')) ∙
            ( ( ap
              ( map-standard-transposition (has-decidable-equality-count eX) np')
              ( q)) ∙
              ( ( ap (λ Y → map-transposition Y i) P) ∙
                ( left-computation-standard-transposition (has-decidable-equality-count eX) np)))))
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inr nq) (inl r) (inl s) t = r
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inr nq) (inl r) (inr ns) t =
      ex-falso
        ( ns
          ( ( inv
            ( left-computation-standard-transposition (has-decidable-equality-count eX) np')) ∙
            ( ( ap
              ( map-standard-transposition (has-decidable-equality-count eX) np')
              ( r)) ∙
              ( ( ap (λ Y → map-transposition Y j) P) ∙
                ( right-computation-standard-transposition (has-decidable-equality-count eX) np)))))
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inr nq) (inr nr) s t =
      ex-falso
        ( contradiction-3-distinct-element-2-Element-Type
          ( 2-element-type-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))
          ( pair i (inl refl))
          ( pair j (inr refl))
          ( pair
            ( x)
            (tr (λ Y → type-decidable-Prop (pr1 Y x)) P (inl refl)))
          ( λ eq → np (pr1 (pair-eq-Σ eq)))
          ( λ eq → nr (inv (pr1 (pair-eq-Σ eq))))
          ( λ eq → nq (inv (pr1 (pair-eq-Σ eq)))))

    eq-orientation-two-elements-count : (i j : X) (np : ¬ (Id i j)) →
      Id
        ( pr1
          ( orientation-two-elements-count i j np
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( j)
    eq-orientation-two-elements-count i j np =
      cases-eq-orientation-two-elements-count i j np
        ( two-elements-transposition eX
          ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))
        ( has-decidable-equality-count eX
          ( pr1
            ( two-elements-transposition eX
              ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
          ( i))
        ( has-decidable-equality-count eX
          ( pr1
          ( two-elements-transposition eX
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
          ( j))
        ( has-decidable-equality-count eX
          ( pr1
          ( pr2
            ( two-elements-transposition eX
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))))
          ( i))
        ( has-decidable-equality-count eX
          ( pr1
            ( pr2
              ( two-elements-transposition eX
                ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))))
          ( j))

  cases-eq-orientation-aut-orientation-two-elements-count-left :
    ( i j : X) (np : ¬ (Id i j)) →
    ( Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( j)) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (¬ (Id x y))
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))
          ( Y)))
      ( pr1 (orientation-two-elements-count i j np Y))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) =
    ( ap
      ( λ Y' →
        pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y')))
      ( inv P ∙
        ( eq-equal-elements-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np')
          ( np)
          ( q)
          ( t)))) ∙
      ( Q ∙
        ( ( inv (eq-orientation-two-elements-count i j np)) ∙
          ( ap
            ( λ Y' → pr1 (orientation-two-elements-count i j np Y'))
            ( ( eq-equal-elements-standard-2-Element-Decidable-Subtype
              (has-decidable-equality-count eX)
              ( np)
              ( np')
              ( inv q)
              ( inv t)) ∙
              ( P)))))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inr nt) =
    ( inward-edge-left-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inl q))
      ( λ s' → np' (q ∙ inv s'))
      ( nt)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count i j np Y y
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inl q))
          ( λ s' → np' (q ∙ inv s'))
          ( nt)))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inl s) t =
    ( ap
      ( λ Y' →
        pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y')))
      ( inv P ∙
        ( ( is-commutative-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np')) ∙
          ( eq-equal-elements-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( λ p → np' (inv p))
            ( np)
            ( s)
            ( r))))) ∙
      ( Q ∙
        ( ( inv (eq-orientation-two-elements-count i j np)) ∙
          ( ap
            ( λ Y' → pr1 (orientation-two-elements-count i j np Y'))
            (  eq-equal-elements-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)
              ( λ p → np' (inv p))
              ( inv s)
              ( inv r) ∙
              ( ( inv
                ( is-commutative-standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))) ∙
                ( P))))))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inr ns) t =
    ( inward-edge-right-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inl r))
      ( ns)
      ( λ t' → np' (r ∙ inv t'))) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count i j np Y y
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inl r))
          ( ns)
          ( λ t' → np' (r ∙ inv t'))))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inl s) t =
    ( inward-edge-left-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inr s))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count i j np Y x
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inr s))
          ( nq)
          ( nr)))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inl t) =
    ( inward-edge-right-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inr t))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count i j np Y x
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inr t))
          ( nq)
          ( nr)))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inr nt) =
    ( ap
      ( λ w →
        pr1
          ( cases-orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)
            ( pr1 w)
            ( pr2 w)
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                (pr1 (pr2 (pr1 w))))
              (pr1 (pr2 (pr1 w))))))
      { x =
        pair
          ( two-elements-transposition eX Y)
          ( has-decidable-equality-count eX
            ( map-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( pr1 (two-elements-transposition eX Y)))
            ( pr1 (two-elements-transposition eX Y)))}
      { y =
        pair
          ( pair x (pair y (pair np' P)))
          ( inl
            ( is-fixed-point-standard-transposition
              ( has-decidable-equality-count eX)
              ( np)
              ( x)
              ( λ q → nq (inv q))
              ( λ r → nr (inv r))))}
      ( eq-pair-Σ
        ( R)
        ( eq-is-prop
          ( is-prop-is-decidable
            ( is-set-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( x))
              ( x)))))) ∙
      (  ap
        ( λ w →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( pair x (pair y (pair np' P)))
              ( pr1 w)
              ( pr2 w)
              ( has-decidable-equality-count eX y i)))
        { x = pair (inr nq) (inr nr)}
        { y =
          pair
            ( has-decidable-equality-count eX x i)
            ( has-decidable-equality-count eX x j)}
        ( eq-pair-Σ
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i)))
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j)))) ∙
        ap
          ( λ k →
            pr1
              ( cases-orientation-two-elements-count i j Y k
                ( has-decidable-equality-count eX (pr1 k) i)
                ( has-decidable-equality-count eX (pr1 k) j)
                ( has-decidable-equality-count eX (pr1 (pr2 k)) i)))
          ( inv R))

  cases-eq-orientation-aut-orientation-two-elements-count-right :
    ( i j : X) (np : ¬ (Id i j)) →
    ( Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( i)) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (¬ (Id x y))
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np))
          ( Y)))
      ( pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) =
    ( ap
      ( λ Y' →
        pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y')))
      ( inv P ∙
        ( eq-equal-elements-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np')
          ( np)
          ( q)
          ( t)))) ∙
      ( Q ∙
        ( ( inv (eq-orientation-two-elements-count j i (λ p → np (inv p)))) ∙
           ap
            ( λ Y' → pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y'))
            ( ( is-commutative-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( λ p → np (inv p))) ∙
              ( ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( λ p → np (inv (inv p)))
                ( np')
                ( inv q)
                ( inv t)) ∙
                ( P)))))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inr nt) =
    ( inward-edge-left-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inl q))
      ( λ s' → np' (q ∙ inv s'))
      ( nt)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count j i (λ p → np (inv p)) Y y
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inl q))
          ( nt)
          ( λ s' → np' (q ∙ inv s'))))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inl s) t =
    ( ap
      ( λ Y' →
        pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y')))
      ( inv P ∙
        ( ( is-commutative-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np')) ∙
          ( eq-equal-elements-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( λ p → np' (inv p))
            ( np)
            ( s)
            ( r))))) ∙
      ( Q ∙
        ( ( inv (eq-orientation-two-elements-count j i (λ p → np (inv p)))) ∙
          ( ap
            ( λ Y' → pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y'))
            ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( λ p → np (inv p))
                ( np')
                ( inv r)
                ( inv s) ∙
                ( P)))))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inr ns) t =
    ( inward-edge-right-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inl r))
      ( ns)
      ( λ t' → np' (r ∙ inv t'))) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count j i (λ p → np (inv p)) Y y
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inl r))
          ( λ t' → np' (r ∙ inv t'))
          ( ns)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inl s) t =
    ( inward-edge-left-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inr s))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count j i (λ p → np (inv p)) Y x
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inr s))
          ( nr)
          ( nq)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inl t) =
    ( inward-edge-right-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inr t))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count j i (λ p → np (inv p)) Y x
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inr t))
          ( nr)
          ( nq)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inr nt) =
    ( ap
      ( λ w →
        pr1
          ( cases-orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)
            ( pr1 w)
            ( pr2 w)
            ( has-decidable-equality-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                (pr1 (pr2 (pr1 w))))
              (pr1 (pr2 (pr1 w))))))
      { x =
        pair
          ( two-elements-transposition eX Y)
          ( has-decidable-equality-count eX
            ( map-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( pr1 (two-elements-transposition eX Y)))
            ( pr1 (two-elements-transposition eX Y)))}
      { y =
        pair
          ( pair x (pair y (pair np' P)))
          ( inl
            ( is-fixed-point-standard-transposition
              ( has-decidable-equality-count eX)
              ( np)
              ( x)
              ( λ q → nq (inv q))
              ( λ r → nr (inv r))))}
      ( eq-pair-Σ
        ( R)
        ( eq-is-prop
          ( is-prop-is-decidable
            ( is-set-count eX
              ( map-equiv
                ( transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np)))
                ( x))
              ( x)))))) ∙
      ( ap
        ( λ w →
          pr1
            ( cases-orientation-two-elements-count j i Y
              ( pair x (pair y (pair np' P)))
              ( pr1 w)
              ( pr2 w)
              ( has-decidable-equality-count eX y j)))
        { x = pair (inr nr) (inr nq)}
        { y =
          pair
            ( has-decidable-equality-count eX x j)
            ( has-decidable-equality-count eX x i)}
        ( eq-pair-Σ
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j)))
          ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i)))) ∙
        ( ap
          ( λ k →
            pr1
              ( cases-orientation-two-elements-count j i Y k
                ( has-decidable-equality-count eX (pr1 k) j)
                ( has-decidable-equality-count eX (pr1 k) i)
                ( has-decidable-equality-count eX (pr1 (pr2 k)) j)))
          ( inv R)))

  cases-eq-orientation-aut-orientation-two-elements-count :
    ( i j : X) (np : ¬ (Id i j)) →
    is-decidable
      ( Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( j)) →
    coprod
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
        ( orientation-two-elements-count i j np))
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
        ( orientation-two-elements-count j i (λ p → np (inv p))))
  cases-eq-orientation-aut-orientation-two-elements-count i j np (inl q) =
    inl
      ( eq-htpy
        ( λ Y →
          eq-pair-Σ
            ( cases-eq-orientation-aut-orientation-two-elements-count-left i j np q Y
              ( two-elements-transposition eX Y)
              ( refl)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) j))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( pr1 Y (pr1 (orientation-two-elements-count i j np Y)))))))
  cases-eq-orientation-aut-orientation-two-elements-count i j np (inr nq) =
    inr
      ( eq-htpy
        ( λ Y →
          eq-pair-Σ
            ( cases-eq-orientation-aut-orientation-two-elements-count-right i j np
              ( q'
                ( has-decidable-equality-count eX
                  ( pr1
                    ( orientation-aut-count
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-count eX)
                          ( np)))
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np))))
                  ( i)))
              ( Y)
              ( two-elements-transposition eX Y)
              ( refl)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) j))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( pr1 Y (pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y)))))))
    where
    q' :
      is-decidable
        ( Id
          ( pr1
            ( orientation-aut-count
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))))
          ( i)) →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( i)
    q' (inl r) = r
    q' (inr nr) =
      ex-falso
        ( contradiction-3-distinct-element-2-Element-Type
          ( 2-element-type-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))
          ( pair i (inl refl))
          ( pair j (inr refl))
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( λ p → np (pr1 (pair-eq-Σ p)))
          ( λ q → nq (pr1 (pair-eq-Σ (inv q))))
          ( λ r → nr (pr1 (pair-eq-Σ (inv r)))))

  eq-orientation-aut-orientation-two-elements-count :
    ( i j : X) (np : ¬ (Id i j)) →
    coprod
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
        ( orientation-two-elements-count i j np))
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
        ( orientation-two-elements-count j i (λ p → np (inv p))))
  eq-orientation-aut-orientation-two-elements-count i j np =
    cases-eq-orientation-aut-orientation-two-elements-count i j np
      (has-decidable-equality-count eX
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( j))

  cases-eq-map-orientation-transposition-orientation-two-elements-count : 
    ( i j : X) (np : ¬ (Id i j)) →
    ( Y : 2-Element-Decidable-Subtype l X) →
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y → Σ (¬ (Id x y))
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    Id (two-elements-transposition eX Y) two-elements →
    is-decidable (Id (pr1 two-elements) i) →
    is-decidable (Id (pr1 two-elements) j) →
    is-decidable (Id (pr1 (pr2 two-elements)) i) →
    is-decidable (Id (pr1 (pr2 two-elements)) j) →
    Id
      ( pr1
        ( map-orientation-complete-undirected-graph-equiv
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( orientation-two-elements-count i j np)
          ( Y)))
      ( pr1 ( orientation-two-elements-count j i (λ p → np (inv p)) Y))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inl q) r s (inl t) =
    ( ap
      ( λ Y' →
        map-inv-equiv
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( pr1
            ( orientation-two-elements-count i j np Y')))
      ( ( ap
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( inv P ∙
          ( eq-equal-elements-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np')
            ( np)
            ( q)
            ( t)))) ∙
        ( eq-transposition-precomp-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np)))) ∙
      ( ( ap
        ( map-inv-equiv
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( eq-orientation-two-elements-count i j np)) ∙
        ( ( ap
          ( λ e → map-equiv e j)
          { x =
            inv-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))}
          ( own-inverse-is-involution
            ( is-involution-map-transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))))) ∙
          ( ( right-computation-standard-transposition (has-decidable-equality-count eX) np) ∙
            ( inv (eq-orientation-two-elements-count j i (λ p → np (inv p))) ∙
              ( ap
              ( λ Y' → pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y'))
              ( ( is-commutative-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( λ p → np (inv p))) ∙
                ( ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( λ p → np (inv (inv p)))
                  ( np')
                  ( inv q)
                  ( inv t)) ∙
                  ( P))))))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inl q) r s (inr nt) =
    ( ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( inward-edge-right-two-elements-orientation-count i j np
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y))
        ( y)
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( y)))
          ( P)
          ( inr
            ( inv
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( y)
                ( λ s' → np' (q ∙ s'))
                ( λ t → nt (inv t))))))
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( j)))
          ( P)
          ( inl
            ( q ∙
              ( inv
                ( right-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np))))))
        ( λ s' → np' (q ∙ inv s'))
        ( nt))) ∙
      ( ( is-fixed-point-standard-transposition
        ( has-decidable-equality-count eX)
        ( np)
        ( y)
        ( λ s' → np' (q ∙ s'))
        ( λ t → nt (inv t))) ∙
        ( inv
          ( inward-edge-right-two-elements-orientation-count j i (λ p → np (inv p)) Y y
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inl q))
            ( nt)
            ( λ s' → np' (q ∙ inv s')))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inl s) t =
    ( ap
      ( λ Y' →
        map-inv-equiv
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( pr1
            ( orientation-two-elements-count i j np Y')))
      ( ( ap
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( inv P ∙
          ( is-commutative-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np') ∙
            ( eq-equal-elements-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( λ p → np' (inv p))
              ( np)
              ( s)
              ( r))))) ∙
        ( eq-transposition-precomp-standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np)))) ∙
      ( ( ap
        ( map-inv-equiv
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( eq-orientation-two-elements-count i j np)) ∙
        ( ( ap
          ( λ e → map-equiv e j)
          { x =
            inv-equiv
              ( transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))}
          ( own-inverse-is-involution
            ( is-involution-map-transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))))) ∙
          ( ( right-computation-standard-transposition (has-decidable-equality-count eX) np) ∙
            ( ( inv (eq-orientation-two-elements-count j i (λ p → np (inv p)))) ∙
              ( ap
                ( λ Y' → pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y'))
                ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( λ p → np (inv p))
                    ( np')
                    ( inv r)
                    ( inv s) ∙
                    ( P)))))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inr ns) t =
     ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( inward-edge-left-two-elements-orientation-count i j np
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y))
        ( y)
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( y)))
          ( P)
          ( inr
            ( inv
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( y)
                ( λ s' → ns (inv s'))
                ( λ t → np' (r ∙ t))))))
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( i)))
          ( P)
          ( inl
            ( r ∙
               inv
                ( left-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np)))))
        ( ns)
        ( λ t → np' (r ∙ inv t))) ∙
      ( ( is-fixed-point-standard-transposition
        ( has-decidable-equality-count eX)
        ( np)
        ( y)
        ( λ s' → ns (inv s'))
        ( λ t → np' (r ∙ t))) ∙
        ( inv
          ( inward-edge-left-two-elements-orientation-count j i (λ p → np (inv p)) Y y
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' y)) P (inr refl))
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inl r))
            ( λ t' → np' (r ∙ inv t'))
            ( ns))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inl s) t =
     ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( inward-edge-right-two-elements-orientation-count i j np
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y))
        ( x)
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( x)))
          ( P)
          ( inl
            ( inv
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( x)
                ( λ q → nq (inv q))
                ( λ r → nr (inv r))))))
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( j)))
          ( P)
          ( inr
            ( s ∙
              ( inv
                ( right-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np))))))
        ( nq)
        ( nr)) ∙
      (  is-fixed-point-standard-transposition
        ( has-decidable-equality-count eX)
        ( np)
        ( x)
        ( λ q → nq (inv q))
        ( λ r → nr (inv r)) ∙
        ( inv
          ( inward-edge-right-two-elements-orientation-count j i (λ p → np (inv p)) Y x
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' i)) P (inr s))
            ( nr)
            ( nq))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inl t) =
    ( ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( inward-edge-left-two-elements-orientation-count i j np
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y))
        ( x)
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( x)))
          ( P)
          ( inl
            ( inv
              ( is-fixed-point-standard-transposition
                ( has-decidable-equality-count eX)
                ( np)
                ( x)
                ( λ q → nq (inv q))
                ( λ r → nr (inv r))))))
        ( tr
          ( λ Y' →
            type-decidable-Prop
              ( ( pr1 Y' ∘
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))))
                ( i)))
          ( P)
          ( inr
            ( t ∙
               inv
                ( left-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np)))))
        ( nq)
        ( nr))) ∙
      ( ( is-fixed-point-standard-transposition
        ( has-decidable-equality-count eX)
        ( np)
        ( x)
        ( λ q → nq (inv q))
        ( λ r → nr (inv r))) ∙
        ( inv
          ( inward-edge-left-two-elements-orientation-count j i (λ p → np (inv p)) Y x
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' x)) P (inl refl))
            ( tr (λ Y' → type-decidable-Prop (pr1 Y' j)) P (inr t))
            ( nr)
            ( nq))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inr ns) (inr nt) =
    ( ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( ( ap
        ( λ Y' →
          pr1
            ( orientation-two-elements-count i j np Y'))
        ( ( ap
          ( precomp-equiv-2-Element-Decidable-Subtype
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))))
          ( inv P)) ∙
          ( ( eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np)
            ( np')
            ( λ q → nq (inv q))
            ( λ s → ns (inv s))
            ( λ r → nr (inv r))
            ( λ t → nt (inv t))) ∙
            ( P)))) ∙
        ( ( ap
          ( λ k →
            pr1
              ( cases-orientation-two-elements-count i j Y k
                ( has-decidable-equality-count eX (pr1 k) i)
                ( has-decidable-equality-count eX (pr1 k) j)
                ( has-decidable-equality-count eX (pr1 (pr2 k)) i)))
          ( R)) ∙
          ( ap
            ( λ w →
              pr1
                ( cases-orientation-two-elements-count i j Y
                  ( pair x (pair y (pair np' P)))
                  ( pr1 w)
                  ( pr2 w)
                  ( has-decidable-equality-count eX y i)))
            { x =
              pair
                ( has-decidable-equality-count eX x i)
                ( has-decidable-equality-count eX x j)}
            { y = pair (inr nq) (inr nr)}
            ( eq-pair-Σ
              ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i)))
              ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j)))))))) ∙
      ( ( is-fixed-point-standard-transposition
        ( has-decidable-equality-count eX)
        ( np)
        ( x)
        ( λ q → nq (inv q))
        ( λ r → nr (inv r))) ∙
        ( ( ap
          ( λ w →
            pr1
              ( cases-orientation-two-elements-count j i Y
                ( pair x (pair y (pair np' P)))
                ( pr1 w)
                ( pr2 w)
                ( has-decidable-equality-count eX y j)))
          { x = pair (inr nr) (inr nq)}
          { y =
            pair
              ( has-decidable-equality-count eX x j)
              ( has-decidable-equality-count eX x i)}
          ( eq-pair-Σ
            ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j)))
            ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i))))) ∙
          ( ap
            ( λ k →
              pr1
                ( cases-orientation-two-elements-count j i Y k
                  ( has-decidable-equality-count eX (pr1 k) j)
                  ( has-decidable-equality-count eX (pr1 k) i)
                  ( has-decidable-equality-count eX (pr1 (pr2 k)) j)))
            ( inv R))))

  eq-map-orientation-transposition-orientation-two-elements-count : 
    ( i j : X) (np : ¬ (Id i j)) →
    Id
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np)))
        ( orientation-two-elements-count i j np))
      ( orientation-two-elements-count j i (λ p → np (inv p)))
  eq-map-orientation-transposition-orientation-two-elements-count i j np =
    eq-htpy
      ( λ Y →
        eq-pair-Σ
          ( cases-eq-map-orientation-transposition-orientation-two-elements-count i j np Y
            ( two-elements-transposition eX Y)
            ( refl)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) i)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX Y)) j)
            ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) i)
            ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX Y))) j))
          ( eq-is-prop
            ( is-prop-type-decidable-Prop
              ( pr1 Y
                ( pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y))))))

  equiv-fin-1-difference-orientation-two-elements-count :
    ( i j : X) (np : ¬ (Id i j)) →
    Fin 1 ≃
    Σ (2-Element-Decidable-Subtype l X)
    ( λ Y → type-decidable-Prop
      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( orientation-two-elements-count i j np)
        ( orientation-two-elements-count j i (λ p → np (inv p)))
        ( Y)))
  pr1 (pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np) x) =
    standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np
  pr2 (pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np) x) q =
    np
      ( ( inv
        ( eq-orientation-two-elements-count j i (λ p → np (inv p)))) ∙
        ( ( ap
          ( λ Y → pr1 (orientation-two-elements-count j i (λ p → np (inv p)) Y))
          { x =
            standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( λ p → np (inv p))}
          { y =
            standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)}
          ( inv
            ( is-commutative-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))) ∙
          ( inv (ap pr1 q) ∙
            eq-orientation-two-elements-count i j np)))
  pr2 (equiv-fin-1-difference-orientation-two-elements-count i j np) =
    is-equiv-has-inverse
      ( λ x → inr star)
      ( λ T →
        eq-pair-Σ
          ( retr-fin-1-difference-orientation-two-elements-count
            ( T)
            ( two-elements-transposition eX (pr1 T))
            ( refl)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX (pr1 T))) i)
            ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX (pr1 T))) j)
            ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) i)
            ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) j))
          ( eq-is-prop
            ( is-prop-type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( orientation-two-elements-count i j np)
                ( orientation-two-elements-count j i (λ p → np (inv p)))
                ( pr1 T)))))
       ( sec-fin-1-difference-orientation-two-elements-count)
    where
    retr-fin-1-difference-orientation-two-elements-count :
      ( T :
        Σ (2-Element-Decidable-Subtype l X)
          (λ Y →
            type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( orientation-two-elements-count i j np)
                ( orientation-two-elements-count j i (λ p → np (inv p)))
                ( Y)))) →
      ( two-elements : Σ X
        ( λ x → Σ X
          ( λ y → Σ (¬ (Id x y))
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( pr1 T))))) →
      Id two-elements (two-elements-transposition eX (pr1 T)) →
      is-decidable (Id (pr1 two-elements) i) →
      is-decidable (Id (pr1 two-elements) j) →
      is-decidable (Id (pr1 (pr2 two-elements)) i) →
      is-decidable (Id (pr1 (pr2 two-elements)) j) →
      Id
        ( standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np))
        ( pr1 T)
    retr-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inl q) r s (inl t) =
        ap
        ( λ w →
          standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            {x = pr1 w}
            {y = j}
            ( pr2 w))
        { x = pair i np}
        { y = pair x (λ p → np (inv q ∙ p))}
        ( eq-pair-Σ
          ( inv q)
          ( eq-is-prop is-prop-neg)) ∙
        ( ( ap
          ( λ w →
            standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              {x = x}
              {y = pr1 w}
              ( pr2 w))
          { x = pair j (λ p → np (inv q ∙ p))}
          { y = pair y np'}
          ( eq-pair-Σ
            ( inv t)
            ( eq-is-prop is-prop-neg))) ∙
          ( P))
    retr-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inl q) r s (inr nt) =
       ex-falso
        ( pr2 T
          ( eq-pair-Σ
            ( ( inward-edge-left-two-elements-orientation-count i j np
              ( pr1 T)
              ( y)
              ( tr
                ( λ Y → type-decidable-Prop (pr1 Y y))
                ( P)
                ( inr refl))
              ( tr
                ( λ z → type-decidable-Prop (pr1 (pr1 T) z))
                ( q)
                ( tr
                  ( λ Y → type-decidable-Prop (pr1 Y x))
                  ( P)
                  ( inl refl)))
              ( λ s → np' (q ∙ inv s))
              ( nt)) ∙
              ( inv
                ( inward-edge-right-two-elements-orientation-count j i
                  ( λ p → np (inv p))
                  ( pr1 T)
                  ( y)
                  ( tr
                    ( λ Y → type-decidable-Prop (pr1 Y y))
                    ( P)
                    ( inr refl))
                  ( tr
                    ( λ z → type-decidable-Prop (pr1 (pr1 T) z))
                    ( q)
                    ( tr
                      ( λ Y → type-decidable-Prop (pr1 Y x))
                      ( P)
                      ( inl refl)))
                  ( nt)
                  ( λ s → np' (q ∙ inv s)))))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( pr1
                  ( pr1 T)
                  ( pr1
                    ( orientation-two-elements-count j i (λ p → np (inv p)) (pr1 T))))))))
    retr-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inr nq) (inl r) (inl s) t =
       ap
        ( λ w →
          standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            {x = pr1 w}
            {y = j}
            ( pr2 w))
        { x = pair i np}
        { y = pair y (λ p → np (inv s ∙ p))}
        ( eq-pair-Σ
          ( inv s)
          ( eq-is-prop is-prop-neg)) ∙
        ( ( ap
          ( λ w →
            standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              {x = y}
              {y = pr1 w}
              ( pr2 w))
          { x = pair j (λ p → np (inv s ∙ p))}
          { y = pair x (λ p → np' (inv p))}
          ( eq-pair-Σ
            ( inv r)
            ( eq-is-prop is-prop-neg))) ∙
          ( inv (is-commutative-standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np') ∙
            ( P)))
    retr-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inr nq) (inl r) (inr ns) t =
       ex-falso
        ( pr2 T
          ( eq-pair-Σ
            (  inward-edge-right-two-elements-orientation-count i j np
              ( pr1 T)
              ( y)
              ( tr
                ( λ Y → type-decidable-Prop (pr1 Y y))
                ( P)
                ( inr refl))
              ( tr
                ( λ z → type-decidable-Prop (pr1 (pr1 T) z))
                ( r)
                ( tr
                  ( λ Y → type-decidable-Prop (pr1 Y x))
                  ( P)
                  ( inl refl)))
              ( ns)
              ( λ t → np' (r ∙ inv t)) ∙
              ( inv
                ( inward-edge-left-two-elements-orientation-count j i
                  ( λ p → np (inv p))
                  ( pr1 T)
                  ( y)
                  ( tr
                    ( λ Y → type-decidable-Prop (pr1 Y y))
                    ( P)
                    ( inr refl))
                  ( tr
                    ( λ z → type-decidable-Prop (pr1 (pr1 T) z))
                    ( r)
                    ( tr
                      ( λ Y → type-decidable-Prop (pr1 Y x))
                      ( P)
                      ( inl refl)))
                  ( λ t → np' (r ∙ inv t))
                  ( ns))))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( pr1
                  ( pr1 T)
                  ( pr1 (orientation-two-elements-count j i (λ p → np (inv p)) (pr1 T))))))))
    retr-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inr nq) (inr nr) s t =
      ex-falso
        ( pr2 T
          ( ap
            ( λ w →
              cases-orientation-two-elements-count i j
                ( pr1 T)
                ( w)
                ( has-decidable-equality-count eX
                  ( pr1 w) i)
                ( has-decidable-equality-count eX
                  (pr1 w) j)
                ( has-decidable-equality-count eX
                  (pr1 (pr2 w)) i))
            ( inv Q) ∙
            ( ( ap
              ( λ D →
                cases-orientation-two-elements-count i j
                  ( pr1 T)
                  ( pair x (pair y (pair np' P)))
                  ( pr1 D)
                  ( pr2 D)
                  ( has-decidable-equality-count eX y i))
              { y = pair (inr nq) (inr nr)}
              ( eq-pair-Σ
                ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i)))
                ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j))))) ∙
              ( ap
                ( λ D →
                  cases-orientation-two-elements-count j i
                    ( pr1 T)
                    (pair x (pair y (pair np' P)))
                    ( pr1 D)
                    ( pr2 D)
                    ( has-decidable-equality-count eX y j))
                { x = pair (inr nr) (inr nq)}
                { y =
                  pair
                    ( has-decidable-equality-count eX x j)
                    ( has-decidable-equality-count eX x i)}
                ( eq-pair-Σ
                  ( eq-is-prop (is-prop-is-decidable (is-set-count eX x j)))
                  ( eq-is-prop (is-prop-is-decidable (is-set-count eX x i)))) ∙
                ( ap
                  ( λ w →
                    cases-orientation-two-elements-count j i
                      ( pr1 T)
                      ( w)
                      ( has-decidable-equality-count eX (pr1 w) j)
                      ( has-decidable-equality-count eX (pr1 w) i)
                      ( has-decidable-equality-count eX (pr1 (pr2 w)) j))
                  ( Q))))))
    sec-fin-1-difference-orientation-two-elements-count :
      ((λ x → inr {A = empty} star) ∘ pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np)) ~ id
    sec-fin-1-difference-orientation-two-elements-count (inr star) = refl

  eq-orientation-pointwise-difference-two-elements-count :
    ( i j : X) (np : ¬ (Id i j)) →
    Id
      1
      ( number-of-elements-is-finite
        ( is-finite-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( orientation-two-elements-count i j np)
          ( orientation-two-elements-count j i (λ p → np (inv p)))))
  eq-orientation-pointwise-difference-two-elements-count i j np =
     ap
      ( number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair
          ( 1)
          ( unit-trunc-Prop (equiv-fin-1-difference-orientation-two-elements-count i j np)))
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( orientation-two-elements-count i j np)
            ( orientation-two-elements-count j i (λ p → np (inv p))))))

  cases-not-even-difference-orientation-aut-transposition-count :
    ( i j : X) (np : ¬ (Id i j)) →
    coprod
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np)))
        ( orientation-two-elements-count i j np))
      ( Id
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
        ( orientation-two-elements-count j i (λ p → np (inv p)))) →
    ¬ ( type-Eq-Rel
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition (standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np)))
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))))
  cases-not-even-difference-orientation-aut-transposition-count i j np (inl pl) =
    tr
      ( λ d →
        ¬ ( type-Eq-Rel
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( d)
          ( map-orientation-complete-undirected-graph-equiv
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( transposition (standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
            ( d))))
      ( inv pl)
      ( tr
        ( λ d →
          ¬ ( type-Eq-Rel
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( orientation-two-elements-count i j np)
            ( d)))
        ( inv
          ( eq-map-orientation-transposition-orientation-two-elements-count i j np))
        ( λ p →
          neq-inl-inr
            ( p ∙
              ( inv
                ( ap mod-two-ℕ
                  ( eq-orientation-pointwise-difference-two-elements-count i j np))))))
  cases-not-even-difference-orientation-aut-transposition-count i j np (inr pr) =
    tr
      ( λ d →
        ¬ ( type-Eq-Rel
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( d)
          ( map-orientation-complete-undirected-graph-equiv
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( transposition (standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
            ( d))))
      ( inv pr)
      ( tr
        ( λ d →
          ¬ ( type-Eq-Rel
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( orientation-two-elements-count j i (λ p → np (inv p)))
            ( d)))
        ( inv
          ( ( ap
            ( λ w →
              map-orientation-complete-undirected-graph-equiv
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( transposition w)
                ( orientation-two-elements-count j i (λ p → np (inv p))))
            ( is-commutative-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))) ∙
            ( eq-map-orientation-transposition-orientation-two-elements-count j i (λ p → np (inv p)))))
        ( λ p →
          neq-inl-inr
            ( p ∙
              ( inv
                ( ap
                  ( mod-two-ℕ)
                  ( eq-orientation-pointwise-difference-two-elements-count j i
                    ( λ p → np (inv p))))))))
    
  not-even-difference-orientation-aut-transposition-count :
    (Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( type-Eq-Rel
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( orientation-aut-count (transposition Y))
      ( map-orientation-complete-undirected-graph-equiv
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( transposition Y)
        ( orientation-aut-count (transposition Y))))
  not-even-difference-orientation-aut-transposition-count Y =
    tr
      ( λ Y' →
        ¬ ( type-Eq-Rel
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( orientation-aut-count (transposition Y'))
          ( map-orientation-complete-undirected-graph-equiv
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( transposition Y')
            ( orientation-aut-count (transposition Y')))))
      ( pr2 (pr2 (pr2 (two-elements-transposition eX Y))))
      ( cases-not-even-difference-orientation-aut-transposition-count
        ( pr1 (two-elements-transposition eX Y))
        ( pr1 (pr2 (two-elements-transposition eX Y)))
        ( pr1 (pr2 (pr2 (two-elements-transposition eX Y))))
        ( eq-orientation-aut-orientation-two-elements-count
          ( pr1 (two-elements-transposition eX Y))
          ( pr1 (pr2 (two-elements-transposition eX Y)))
          ( pr1 (pr2 (pr2 (two-elements-transposition eX Y))))))

  inv-orientation :
    (T : quotient-sign (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( type-class-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( canonical-orientation-count)) →
    Fin 2
  inv-orientation T (inl P) = inl (inr star)
  inv-orientation T (inr NP) = inr star

  equiv-fin-2-quotient-sign-count : Fin 2 ≃
    (quotient-sign (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
  pr1 equiv-fin-2-quotient-sign-count (inl (inr star)) =
    quotient-map-large-set-quotient
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( canonical-orientation-count)
  pr1 equiv-fin-2-quotient-sign-count (inr star) =
    quotient-map-large-set-quotient
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( trans-canonical-orientation-count)
  pr2 equiv-fin-2-quotient-sign-count =
    is-equiv-has-inverse
      ( λ T →
        inv-orientation
          ( T)
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count)))
      ( λ T →
        retr-orientation
          ( T)
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count)))
      ( λ k →
        sec-orientation
          k
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( pr1 equiv-fin-2-quotient-sign-count k)
            ( canonical-orientation-count)))
    where
    cases-retr-orientation :
      (T :
        large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))) →
      ¬ ( type-class-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          (number-of-elements-count eX)
          (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( canonical-orientation-count)) →
      ( t :
        orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      Id
        ( quotient-map-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( t))
        ( T) →
      ( k : Fin 2) →
      Id
        ( k)
        ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( t)
          ( canonical-orientation-count)) →
      type-class-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( trans-canonical-orientation-count) 
    cases-retr-orientation T NH t q (inl (inr star)) r =
      ex-falso
        ( NH
          ( tr
            ( λ x →
              type-class-large-set-quotient
                ( even-difference-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( x)
                ( canonical-orientation-count))
            ( q)
            ( r)))
    cases-retr-orientation T NH t q (inr star) r =
      tr
        (λ x →
          type-class-large-set-quotient
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( x)
            ( trans-canonical-orientation-count))
        ( q)
        ( eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( t)
            ( canonical-orientation-count)
            ( trans-canonical-orientation-count)
            ( inr star)
            ( r)
            ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( trans-canonical-orientation-count)
              ( canonical-orientation-count)
              ( inr star)
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( canonical-orientation-count)
                  ( trans-canonical-orientation-count)
                  ( inr star)
                  (ap
                    ( mod-two-ℕ)
                    { x = 1}
                    { y =
                      number-of-elements-is-finite
                        ( is-finite-subtype-pointwise-difference
                          ( number-of-elements-count eX)
                          ( pair X (unit-trunc-Prop (equiv-count eX)))
                          ( canonical-orientation-count)
                          ( trans-canonical-orientation-count))}
                    ( eq-orientation-pointwise-difference-two-elements-count
                      ( first-element-count)
                      ( second-element-count)
                      ( distinct-two-elements-count))))))
    retr-orientation :
      (T :
        quotient-sign
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      (H :
        is-decidable
          (type-class-large-set-quotient
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count))) →
      Id (pr1 equiv-fin-2-quotient-sign-count (inv-orientation T H)) T
    retr-orientation T (inl H) =
      eq-effective-quotient'
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( canonical-orientation-count)
        ( T)
        ( H)
    retr-orientation T (inr NH) =
      eq-effective-quotient'
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( trans-canonical-orientation-count)
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( pair
            ( type-class-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( trans-canonical-orientation-count))
            ( is-prop-type-class-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( trans-canonical-orientation-count)))
          ( λ (pair t r) →
            cases-retr-orientation
              ( T)
              ( NH)
              ( t)
              ( eq-pair-Σ
                ( r)
                ( all-elements-equal-type-trunc-Prop _ (pr2 T)))
              ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( t)
                  ( canonical-orientation-count))
              ( refl)))
    sec-orientation : (k : Fin 2) →
      ( D : is-decidable
        ( type-class-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( pr1 equiv-fin-2-quotient-sign-count k)
          ( canonical-orientation-count))) →
      Id
        ( inv-orientation
          ( pr1 equiv-fin-2-quotient-sign-count k)
          ( D))
        ( k)
    sec-orientation (inl (inr star)) (inl Q) = refl
    sec-orientation (inl (inr star)) (inr NQ) =
      ex-falso
        ( NQ
          ( refl-Eq-Rel
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))))
    sec-orientation (inr star) (inl Q) =
      ex-falso
        ( neq-inl-inr
          ( Q ∙
            inv
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( canonical-orientation-count)
                  ( trans-canonical-orientation-count)
                  ( inr star)
                  ( ap mod-two-ℕ
                    ( eq-orientation-pointwise-difference-two-elements-count
                      ( first-element-count)
                      ( second-element-count)
                      ( distinct-two-elements-count))))))
    sec-orientation (inr star) (inr NQ) = refl

module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (ineq : leq-ℕ 2 n)
  where
  
  equiv-fin-2-quotient-sign-equiv-Fin : (h : Fin n ≃ type-UU-Fin-Level X) →
    ( Fin 2 ≃ quotient-sign n X)
  equiv-fin-2-quotient-sign-equiv-Fin h =
    tr
      ( λ e → Fin 2 ≃ quotient-sign n (pair (type-UU-Fin-Level X) e))
      ( all-elements-equal-type-trunc-Prop (unit-trunc-Prop (equiv-count (pair n h))) (pr2 X))
      ( equiv-fin-2-quotient-sign-count (pair n h) ineq)
    
  abstract
    mere-equiv-fin-2-quotient-sign :
      mere-equiv (Fin 2) (quotient-sign n X)
    mere-equiv-fin-2-quotient-sign =
      map-trunc-Prop
        ( equiv-fin-2-quotient-sign-equiv-Fin)
        ( has-cardinality-type-UU-Fin-Level X)
```
