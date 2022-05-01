---
title: Orientations of the complete undirected graph
---

```agda
{-# OPTIONS --without-K --exact-split #-}

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
  ( map-transposition; map-transposition'; transposition; two-elements-transposition;
    left-computation-standard-transposition;
    right-computation-standard-transposition;
    map-standard-transposition; standard-transposition;
    eq-transposition-precomp-standard-2-Element-Decidable-Subtype;
    is-fixed-point-standard-transposition; eq-two-elements-transposition;
    is-involution-map-transposition)

open import foundation.automorphisms using (Aut)
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
    left-unit-law-equiv; right-unit-law-equiv; equiv-comp; is-equiv)
open import foundation.equivalence-classes using
  ( large-set-quotient; quotient-map-large-set-quotient; large-quotient-Set;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient'; is-prop-type-class-large-set-quotient)
open import foundation.equivalence-relations using
  ( Eq-Rel; prop-Eq-Rel; type-Eq-Rel; trans-Eq-Rel; refl-Eq-Rel)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; ap; ap-binary; _∙_; tr)
open import foundation.injective-maps using
  ( is-injective; is-prop-is-injective; is-injective-map-equiv)
open import foundation.intersection using (intersection-decidable-subtype)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.logical-equivalences using (equiv-iff)
open import foundation.mere-equivalences using (transitive-mere-equiv; mere-equiv)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop;
    trunc-Prop; type-trunc-Prop; all-elements-equal-type-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; is-prop; type-Prop; is-prop-function-type; eq-is-prop)
open import foundation.sets using (Id-Prop; UU-Set)
open import foundation.subtypes using (subtype; eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.universal-property-propositional-truncation-into-sets using
  (map-universal-property-set-quotient-trunc-Prop)
open import foundation.unit-type using (star)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; is-finite-2-Element-Decidable-Subtype;
    2-element-type-2-Element-Decidable-Subtype; precomp-equiv-2-Element-Decidable-Subtype;
    standard-2-Element-Decidable-Subtype; 2-element-type-standard-2-Element-Decidable-Subtype;
    is-commutative-standard-2-Element-Decidable-Subtype)
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

  abstract
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
                ( ap ( λ n → add-ℕ ( n) (nat-Fin m)) ( inv ( left-unit-law-mul-ℕ (nat-Fin m)))))
              ( scalar-invariant-cong-ℕ' 2 2 0 (nat-Fin m) (cong-zero-ℕ' 2))))
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
```

```
module _
  {l : Level} {X : UU l} (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where
 
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

  equiv-Fin-1-difference-canonical-orientation-count-trans :
    Fin 1 ≃
    Σ (2-Element-Decidable-Subtype l X)
    ( λ Y → type-decidable-Prop
      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))
        ( canonical-orientation-count)
        ( trans-canonical-orientation-count)
        ( Y)))
  equiv-Fin-1-difference-canonical-orientation-count-trans =
    pair
      ( λ x → pair 
        ( canonical-2-Element-Decidable-Subtype-count)
        ( λ q → distinct-two-elements-count
          ( ( inv
            ( eq-orientation-two-elements-count
              ( second-element-count)
              ( first-element-count)
              ( λ p → distinct-two-elements-count (inv p)))) ∙
            ( ( ap
              ( λ Y → pr1 (trans-canonical-orientation-count Y))
              { x =
                standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( λ p → distinct-two-elements-count (inv p))}
              { y = canonical-2-Element-Decidable-Subtype-count}
              ( inv
                ( is-commutative-standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX) ( distinct-two-elements-count)))) ∙
              ( inv (ap pr1 q) ∙
                eq-orientation-two-elements-count
                  ( first-element-count)
                  ( second-element-count)
                  ( distinct-two-elements-count))))))
      ( is-equiv-has-inverse
        ( λ x → inr star)
        ( λ T →
          eq-pair-Σ
            ( retr-Fin-1-difference-canonical-orientation-count-trans
              ( T)
              ( two-elements-transposition eX (pr1 T))
              ( refl)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX (pr1 T))) first-element-count)
              ( has-decidable-equality-count eX (pr1 (two-elements-transposition eX (pr1 T))) second-element-count)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) first-element-count)
              ( has-decidable-equality-count eX (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) second-element-count))
            ( eq-is-prop
              ( is-prop-type-decidable-Prop
                ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( canonical-orientation-count)
                  ( trans-canonical-orientation-count)
                  ( pr1 T)))))
        ( sec-Fin-1-difference-canonical-orientation-count-trans))
    where
    retr-Fin-1-difference-canonical-orientation-count-trans :
      ( T :
        Σ (2-Element-Decidable-Subtype l X)
          (λ Y →
            type-decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( canonical-orientation-count)
                ( trans-canonical-orientation-count)
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
      is-decidable (Id (pr1 two-elements) first-element-count) →
      is-decidable (Id (pr1 two-elements) second-element-count) →
      is-decidable (Id (pr1 (pr2 two-elements)) first-element-count) →
      is-decidable (Id (pr1 (pr2 two-elements)) second-element-count) →
      Id canonical-2-Element-Decidable-Subtype-count (pr1 T)
    retr-Fin-1-difference-canonical-orientation-count-trans
      T (pair x (pair y (pair np P))) Q (inl q) r s (inl t) =
       ap
        ( λ w →
          standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            {x = pr1 w}
            {y = second-element-count}
            ( pr2 w))
        { x = pair first-element-count distinct-two-elements-count}
        { y = pair x (λ p → distinct-two-elements-count (inv q ∙ p))}
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
          { x = pair second-element-count (λ p → distinct-two-elements-count (inv q ∙ p))}
          { y = pair y np}
          ( eq-pair-Σ
            ( inv t)
            ( eq-is-prop is-prop-neg))) ∙
          ( P))
    retr-Fin-1-difference-canonical-orientation-count-trans
      T (pair x (pair y (pair np P))) Q (inl q) r s (inr nt) =
      ex-falso
        ( pr2 T
          ( eq-pair-Σ
            ( ( inward-edge-left-two-elements-orientation-count
              ( first-element-count)
              ( second-element-count)
              ( distinct-two-elements-count)
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
              ( λ s → np (q ∙ inv s))
              ( nt)) ∙
              ( inv
                ( inward-edge-right-two-elements-orientation-count
                  ( second-element-count)
                  ( first-element-count)
                  ( λ p → distinct-two-elements-count (inv p))
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
                  ( λ s → np (q ∙ inv s)))))
            ( eq-is-prop (is-prop-type-decidable-Prop (pr1 (pr1 T) (pr1 (trans-canonical-orientation-count (pr1 T))))))))
    retr-Fin-1-difference-canonical-orientation-count-trans
      T (pair x (pair y (pair np P))) Q (inr nq) (inl r) (inl s) t =
      ( ap
        ( λ w →
          standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            {x = pr1 w}
            {y = second-element-count}
            ( pr2 w))
        { x = pair first-element-count distinct-two-elements-count}
        { y = pair y (λ p → distinct-two-elements-count (inv s ∙ p))}
        ( eq-pair-Σ
          ( inv s)
          ( eq-is-prop is-prop-neg))) ∙
        ( ( ap
          ( λ w →
            standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              {x = y}
              {y = pr1 w}
              ( pr2 w))
          { x =
            pair
              ( second-element-count)
              ( λ p → distinct-two-elements-count (inv s ∙ p))}
          { y = pair x (λ p → np (inv p))}
          ( eq-pair-Σ
            ( inv r)
            ( eq-is-prop is-prop-neg))) ∙
          ( inv (is-commutative-standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np) ∙
            ( P)))
    retr-Fin-1-difference-canonical-orientation-count-trans
      T (pair x (pair y (pair np P))) Q (inr nq) (inl r) (inr ns) t =
      ex-falso
        ( pr2 T
          ( eq-pair-Σ
            (  inward-edge-right-two-elements-orientation-count
              ( first-element-count)
              ( second-element-count)
              ( distinct-two-elements-count)
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
              ( λ t → np (r ∙ inv t)) ∙
              ( inv
                ( inward-edge-left-two-elements-orientation-count
                  ( second-element-count)
                  ( first-element-count)
                  ( λ p → distinct-two-elements-count (inv p))
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
                  ( λ t → np (r ∙ inv t))
                  ( ns))))
            ( eq-is-prop (is-prop-type-decidable-Prop (pr1 (pr1 T) (pr1 (trans-canonical-orientation-count (pr1 T))))))))
    retr-Fin-1-difference-canonical-orientation-count-trans
      T (pair x (pair y (pair np P))) Q (inr nq) (inr nr) s t =
      ex-falso
        ( pr2 T
          ( ap
            ( λ w →
              cases-orientation-two-elements-count
                ( first-element-count)
                ( second-element-count)
                ( pr1 T)
                ( w)
                ( has-decidable-equality-count eX
                  ( pr1 w) first-element-count)
                ( has-decidable-equality-count eX
                  (pr1 w) second-element-count)
                ( has-decidable-equality-count eX
                  (pr1 (pr2 w)) first-element-count))
            ( inv Q) ∙
            ( ap
              ( λ D →
                cases-orientation-two-elements-count
                  ( first-element-count)
                  ( second-element-count)
                  ( pr1 T)
                  ( pair x (pair y (pair np P)))
                  ( pr1 D)
                  ( pr2 D)
                  ( has-decidable-equality-count eX y first-element-count))
              { y = pair (inr nq) (inr nr)}
              ( eq-pair-Σ
                ( eq-is-prop (is-prop-is-decidable (is-set-count eX x first-element-count)))
                ( eq-is-prop (is-prop-is-decidable (is-set-count eX x second-element-count)))) ∙
              ( ap
                ( λ D →
                  cases-orientation-two-elements-count
                    ( second-element-count)
                    ( first-element-count)
                    ( pr1 T)
                    ( pair x (pair y (pair np P)))
                    ( pr1 D)
                    ( pr2 D)
                    ( has-decidable-equality-count eX y second-element-count))
                { x = pair (inr nr) (inr nq)}
                { y =
                  pair
                    ( has-decidable-equality-count eX x second-element-count)
                    ( has-decidable-equality-count eX x first-element-count)}
                ( eq-pair-Σ
                  ( eq-is-prop (is-prop-is-decidable (is-set-count eX x second-element-count)))
                  ( eq-is-prop (is-prop-is-decidable (is-set-count eX x first-element-count)))) ∙
                ( ap
                  ( λ w →
                    cases-orientation-two-elements-count
                      ( second-element-count)
                      ( first-element-count)
                      ( pr1 T)
                      ( w)
                      ( has-decidable-equality-count eX (pr1 w) second-element-count)
                      ( has-decidable-equality-count eX (pr1 w) first-element-count)
                      ( has-decidable-equality-count eX (pr1 (pr2 w)) second-element-count))
                  ( Q))))))
    sec-Fin-1-difference-canonical-orientation-count-trans :
      ((λ x → inr {A = empty} star) ∘ pr1 equiv-Fin-1-difference-canonical-orientation-count-trans) ~ id
    sec-Fin-1-difference-canonical-orientation-count-trans (inr star) = refl

  eq-canonical-orientation-pointwise-difference-count :
    Id
      1
      ( number-of-elements-is-finite
        ( is-finite-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( canonical-orientation-count)
          ( trans-canonical-orientation-count)))
  eq-canonical-orientation-pointwise-difference-count =
    ap
      ( number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair
          ( 1)
          ( unit-trunc-Prop equiv-Fin-1-difference-canonical-orientation-count-trans))
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( canonical-orientation-count)
            ( trans-canonical-orientation-count))))

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

  equiv-Fin-2-quotient-sign-count : Fin 2 ≃
    (quotient-sign (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
  pr1 equiv-Fin-2-quotient-sign-count (inl (inr star)) =
    quotient-map-large-set-quotient
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( canonical-orientation-count)
  pr1 equiv-Fin-2-quotient-sign-count (inr star) =
    quotient-map-large-set-quotient
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( trans-canonical-orientation-count)
  pr2 equiv-Fin-2-quotient-sign-count =
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
            ( pr1 equiv-Fin-2-quotient-sign-count k)
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
                    ( eq-canonical-orientation-pointwise-difference-count)))))
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
      Id (pr1 equiv-Fin-2-quotient-sign-count (inv-orientation T H)) T
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
          ( pr1 equiv-Fin-2-quotient-sign-count k)
          ( canonical-orientation-count))) →
      Id
        ( inv-orientation
          ( pr1 equiv-Fin-2-quotient-sign-count k)
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
                  ( ap mod-two-ℕ eq-canonical-orientation-pointwise-difference-count))))
    sec-orientation (inr star) (inr NQ) = refl

module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (ineq : leq-ℕ 2 n)
  where
  
  equiv-Fin-2-quotient-sign-equiv-Fin-n : (h : Fin n ≃ type-UU-Fin-Level X) →
    ( Fin 2 ≃ quotient-sign n X)
  equiv-Fin-2-quotient-sign-equiv-Fin-n h =
    tr
      ( λ e → Fin 2 ≃ quotient-sign n (pair (type-UU-Fin-Level X) e))
      ( all-elements-equal-type-trunc-Prop (unit-trunc-Prop (equiv-count (pair n h))) (pr2 X))
      ( equiv-Fin-2-quotient-sign-count (pair n h) ineq)
    
  mere-equiv-Fin-2-quotient-sign :
    mere-equiv (Fin 2) (quotient-sign n X)
  mere-equiv-Fin-2-quotient-sign =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin-Level X)
      ( trunc-Prop (Fin 2 ≃ (quotient-sign n X)))
      ( λ h → unit-trunc-Prop (equiv-Fin-2-quotient-sign-equiv-Fin-n h))
```
