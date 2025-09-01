# Orientations of the complete undirected graph

```agda
{-# OPTIONS --lossy-unification #-}

module univalent-combinatorics.orientations-complete-undirected-graph where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.transpositions

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.intersections-subtypes
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.symmetric-difference
```

</details>

```agda
module _
  {l : Level} (n : ℕ) (X : Type-With-Cardinality-ℕ l n)
  where

  orientation-Complete-Undirected-Graph : UU (lsuc l)
  orientation-Complete-Undirected-Graph =
    ( (P , H) :
        2-Element-Decidable-Subtype l (type-Type-With-Cardinality-ℕ n X)) →
    Σ (type-Type-With-Cardinality-ℕ n X) (type-Decidable-Prop ∘ P)

  is-set-orientation-Complete-Undirected-Graph :
    is-set orientation-Complete-Undirected-Graph
  is-set-orientation-Complete-Undirected-Graph =
    is-set-Π
      ( λ (P , H) →
        is-set-Σ
          ( is-set-type-Type-With-Cardinality-ℕ n X)
          ( λ x → is-set-is-prop (is-prop-type-Decidable-Prop (P x))))

  2-Element-Decidable-Subtype-subtype-pointwise-difference :
    orientation-Complete-Undirected-Graph →
    orientation-Complete-Undirected-Graph →
    2-Element-Decidable-Subtype l (type-Type-With-Cardinality-ℕ n X) →
    Decidable-Prop l
  pr1 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y) =
    d Y ≠ d' Y
  pr1 (pr2 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)) =
    is-prop-neg
  pr2 (pr2 (2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)) =
    is-decidable-neg
      ( has-decidable-equality-is-finite
        ( is-finite-type-decidable-subtype
          ( pr1 Y)
          ( is-finite-type-Type-With-Cardinality-ℕ n X))
        ( d Y)
        ( d' Y))
  is-finite-subtype-pointwise-difference :
    (d d' : orientation-Complete-Undirected-Graph) →
    is-finite
      ( Σ
        ( 2-Element-Decidable-Subtype l (type-Type-With-Cardinality-ℕ n X))
        ( λ Y →
          type-Decidable-Prop
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d d' Y)))
  is-finite-subtype-pointwise-difference d d' =
    is-finite-type-decidable-subtype
      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d d')
      ( is-finite-2-Element-Decidable-Subtype n X)
  mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    orientation-Complete-Undirected-Graph →
    orientation-Complete-Undirected-Graph → Fin 2
  mod-two-number-of-differences-orientation-Complete-Undirected-Graph d d' =
    mod-two-ℕ (number-of-elements-is-finite
      ( is-finite-subtype-pointwise-difference d d'))
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
            ( prop-Decidable-Prop
              ( symmetric-difference-decidable-subtype
                ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                  d1 d2)
                ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                  d2 d3)
                ( Y)))
            ( prop-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                d1 d3 Y))
            ( f Y)
            ( g Y))
      where
      f :
        (Y :
          2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X)) →
        type-Prop
          ( prop-Decidable-Prop
            ( symmetric-difference-decidable-subtype
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3)
              ( Y))) →
          type-Prop
            ( prop-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                d1 d3 Y))
      f Y (inl (pair np nnq)) r =
        np (r ∙
          inv
            ( double-negation-elim-is-decidable
              ( has-decidable-equality-is-finite
                ( is-finite-type-decidable-subtype
                  ( pr1 Y)
                  ( is-finite-type-Type-With-Cardinality-ℕ n X))
                ( d2 Y)
                ( d3 Y))
              ( nnq)))
      f Y (inr (pair nq nnp)) r =
        nq
          ( ( inv
              ( double-negation-elim-is-decidable
                ( has-decidable-equality-is-finite
                  ( is-finite-type-decidable-subtype
                    ( pr1 Y)
                    ( is-finite-type-Type-With-Cardinality-ℕ n X))
                  ( d1 Y)
                  ( d2 Y))
                ( nnp))) ∙
            ( r))
      cases-g :
        (Y :
          2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X)) →
        d1 Y ≠ d3 Y → (is-decidable (d1 Y ＝ d2 Y)) →
        is-decidable (d2 Y ＝ d3 Y) →
        ((d1 Y ≠ d2 Y) × ¬ (d2 Y ≠ d3 Y)) +
        ((d2 Y ≠ d3 Y) × ¬ (d1 Y ≠ d2 Y))
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
      g :
        (Y :
          2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X)) →
        type-Decidable-Prop
          ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d3 Y) →
        type-Decidable-Prop
          ( symmetric-difference-decidable-subtype
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3) Y)
      g Y r =
        cases-g Y r
          ( has-decidable-equality-is-finite
            ( is-finite-type-decidable-subtype
              ( pr1 Y)
              ( is-finite-type-Type-With-Cardinality-ℕ n X))
            ( d1 Y)
            ( d2 Y))
          ( has-decidable-equality-is-finite
            ( is-finite-type-decidable-subtype
              ( pr1 Y)
              ( is-finite-type-Type-With-Cardinality-ℕ n X))
            ( d2 Y)
            ( d3 Y))
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    ( d d' : orientation-Complete-Undirected-Graph) (m : Fin 2) →
    Id
      ( m)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        d d') →
    Id
      ( m)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        d' d)
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
    d d' m p =
    ( p) ∙
    ( ap
      ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( has-finite-cardinality-d'-d)
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference d' d))))
    where
    has-finite-cardinality-d'-d :
      has-finite-cardinality
        ( Σ ( 2-Element-Decidable-Subtype l
              ( type-Type-With-Cardinality-ℕ n X))
            ( λ Y →
              type-Decidable-Prop
                ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                  d' d Y)))
    pr1 has-finite-cardinality-d'-d =
      pr1
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference d d'))
    pr2 has-finite-cardinality-d'-d =
      apply-universal-property-trunc-Prop
        ( pr2
          ( has-finite-cardinality-is-finite
            ( is-finite-subtype-pointwise-difference d d')))
        ( trunc-Prop
          ( ( Fin (pr1 has-finite-cardinality-d'-d)) ≃
            ( Σ ( 2-Element-Decidable-Subtype l
                  ( type-Type-With-Cardinality-ℕ n X))
                ( λ Y → d' Y ≠ d Y))))
        ( λ h → unit-trunc-Prop (h' ∘e h))
      where
      h' :
        Σ ( 2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X))
          ( λ Y → d Y ≠ d' Y) ≃
        Σ ( 2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X))
          ( λ Y → d' Y ≠ d Y)
      pr1 h' (pair Y np) = pair Y (λ p' → np (inv p'))
      pr2 h' =
        is-equiv-is-invertible
          ( λ (pair Y np) → pair Y (λ p' → np (inv p')))
          ( λ (pair Y np) → eq-pair-eq-fiber (eq-is-prop is-prop-neg))
          ( λ (pair Y np) → eq-pair-eq-fiber (eq-is-prop is-prop-neg))
  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph :
    (d1 d2 d3 : orientation-Complete-Undirected-Graph) (m : Fin 2) →
    Id
      ( m)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        d1 d2) →
    Id
      ( m)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        d2 d3) →
    Id
      ( zero-Fin 1)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
        d1 d3)
  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
    d1 d2 d3 m p1 p2 =
    inv
      ( is-zero-mod-succ-ℕ
        ( 1)
        ( dist-ℕ (k1 +ℕ k2) (2 *ℕ k'))
        ( transitive-cong-ℕ
          ( 2)
          ( k1 +ℕ k2)
          ( zero-ℕ)
          ( 2 *ℕ k')
          ( scalar-invariant-cong-ℕ' 2 0 2 k' (cong-zero-ℕ' 2))
          ( transitive-cong-ℕ 2
            ( k1 +ℕ k2)
            ( add-ℕ
              ( nat-Fin 2
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                    d1 d2))
              ( nat-Fin 2
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                    d2 d3)))
            ( zero-ℕ)
            ( concatenate-eq-cong-ℕ 2
              ( ( ap-binary
                  ( add-ℕ)
                  ( ap (nat-Fin 2) (inv p1))
                  ( ap (nat-Fin 2) (inv p2))) ∙
                ( ap
                  ( λ n → n +ℕ (nat-Fin 2 m))
                  ( inv (left-unit-law-mul-ℕ (nat-Fin 2 m)))))
              ( scalar-invariant-cong-ℕ' 2 2 0 (nat-Fin 2 m) (cong-zero-ℕ' 2)))
            ( symmetric-cong-ℕ 2
              ( add-ℕ
                ( nat-Fin 2
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                      d1 d2))
                ( nat-Fin 2
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                      d2 d3)))
              ( k1 +ℕ k2)
              ( cong-add-ℕ k1 k2))))) ∙
      ( ap
        ( mod-two-ℕ)
        ( ( symmetric-dist-ℕ (k1 +ℕ k2) (2 *ℕ k')) ∙
          ( inv
            ( rewrite-left-add-dist-ℕ
              ( k)
              ( 2 *ℕ k')
              ( k1 +ℕ k2)
              ( inv
                ( eq-symmetric-difference
                  ( 2-Element-Decidable-Subtype l
                    ( type-Type-With-Cardinality-ℕ n X))
                  ( is-finite-2-Element-Decidable-Subtype n X)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                      d1 d2)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                      d2 d3)))) ∙
            ( ap
              ( number-of-elements-has-finite-cardinality)
              ( all-elements-equal-has-finite-cardinality
                ( has-finite-cardinality-is-finite
                  ( is-finite-type-decidable-subtype
                    ( symmetric-difference-decidable-subtype
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                          d1 d2)
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                          d2 d3))
                    ( is-finite-2-Element-Decidable-Subtype n X)))
                ( pair
                  ( number-of-elements-is-finite
                    ( is-finite-type-decidable-subtype
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                          d1 d3)
                      ( is-finite-2-Element-Decidable-Subtype n X)))
                  ( transitive-mere-equiv _ _ _
                    ( unit-trunc-Prop
                      ( inv-equiv
                        ( equiv-symmetric-difference-subtype-pointwise-difference
                            d1 d2 d3)))
                    ( pr2
                      ( has-finite-cardinality-is-finite
                        ( is-finite-type-decidable-subtype
                          ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                              d1 d3)
                          ( is-finite-2-Element-Decidable-Subtype n X)))))))))))
    where
    k : ℕ
    k =
      number-of-elements-is-finite
        ( is-finite-type-decidable-subtype
          ( symmetric-difference-decidable-subtype
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                d2 d3))
          ( is-finite-2-Element-Decidable-Subtype n X))
    k1 : ℕ
    k1 =
      number-of-elements-is-finite
        (is-finite-subtype-pointwise-difference d1 d2)
    k2 : ℕ
    k2 =
      number-of-elements-is-finite
        (is-finite-subtype-pointwise-difference d2 d3)
    k' : ℕ
    k' =
      number-of-elements-is-finite
        ( is-finite-type-decidable-subtype
          ( intersection-decidable-subtype
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d1 d2)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-difference d2 d3))
          ( is-finite-2-Element-Decidable-Subtype n X))
  even-difference-orientation-Complete-Undirected-Graph :
    equivalence-relation lzero orientation-Complete-Undirected-Graph
  pr1 even-difference-orientation-Complete-Undirected-Graph d d' =
    Id-Prop
      ( Fin-Set 2)
      ( zero-Fin 1)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
          d d')
  pr1 (pr2 even-difference-orientation-Complete-Undirected-Graph) d =
    ap
      ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair
          ( 0)
          ( unit-trunc-Prop (equiv-is-empty id (λ (_ , np) → np refl))))
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference d d)))
  pr1 (pr2 (pr2 even-difference-orientation-Complete-Undirected-Graph))
    d d' p =
    is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
      d d' (zero-Fin 1) p
  pr2 (pr2 (pr2 even-difference-orientation-Complete-Undirected-Graph))
    d1 d2 d3 p1 p2 =
    eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
      d1 d2 d3 (zero-Fin 1) p2 p1
  abstract
    is-decidable-even-difference-orientation-Complete-Undirected-Graph :
      (Y Y' : orientation-Complete-Undirected-Graph) →
      is-decidable
        ( sim-equivalence-relation
            ( even-difference-orientation-Complete-Undirected-Graph)
            ( Y)
            ( Y'))
    is-decidable-even-difference-orientation-Complete-Undirected-Graph Y Y' =
      has-decidable-equality-is-finite
        ( is-finite-Fin 2)
        ( zero-Fin 1)
        ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
            Y Y')
  quotient-sign : UU (lsuc l)
  quotient-sign =
    equivalence-class even-difference-orientation-Complete-Undirected-Graph
  quotient-sign-Set : Set (lsuc l)
  quotient-sign-Set =
    equivalence-class-Set even-difference-orientation-Complete-Undirected-Graph
module _
  {l : Level} (n : ℕ)
  where
  map-orientation-complete-undirected-graph-equiv :
    (X X' : Type-With-Cardinality-ℕ l n) →
    ( type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
    orientation-Complete-Undirected-Graph n X →
    orientation-Complete-Undirected-Graph n X'
  pr1 (map-orientation-complete-undirected-graph-equiv X X' e d Y) =
    map-equiv e (pr1 (d (precomp-equiv-2-Element-Decidable-Subtype e Y)))
  pr2 (map-orientation-complete-undirected-graph-equiv X X' e d Y) =
    pr2 (d (precomp-equiv-2-Element-Decidable-Subtype e Y))
  orientation-complete-undirected-graph-equiv :
    (X X' : Type-With-Cardinality-ℕ l n) →
    ( type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
    orientation-Complete-Undirected-Graph n X ≃
    orientation-Complete-Undirected-Graph n X'
  pr1 (orientation-complete-undirected-graph-equiv X X' e) =
    map-orientation-complete-undirected-graph-equiv X X' e
  pr2 (orientation-complete-undirected-graph-equiv X X' e) =
    is-equiv-is-invertible
      ( map-orientation-complete-undirected-graph-equiv X' X (inv-equiv e))
      ( λ d →
        eq-htpy
          ( λ Y →
            eq-pair-Σ
              (( ( ap
                ( λ Y' → (map-equiv e ∘ (map-equiv (inv-equiv e))) (pr1 (d Y')))
                ( eq-pair-Σ
                  ( ap
                    ( λ h → pr1 Y ∘ map-equiv h)
                    ( left-inverse-law-equiv (inv-equiv e)))
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( ap
                  ( λ h → map-equiv h (pr1 (d Y)))
                  ( left-inverse-law-equiv (inv-equiv e)))))
              ( eq-is-prop
                ( is-prop-type-Decidable-Prop (pr1 Y (pr1 (id d Y)))))))
      ( λ d →
        eq-htpy
          ( λ Y →
            eq-pair-Σ
              ( ( ap
                ( λ Y' → (map-equiv (inv-equiv e) ∘ map-equiv e) (pr1 (d Y')))
                ( eq-pair-Σ
                  ( ap
                    ( λ h → pr1 Y ∘ map-equiv h)
                    ( right-inverse-law-equiv (inv-equiv e)))
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( ap
                  ( λ h → map-equiv h (pr1 (d Y)))
                  ( right-inverse-law-equiv (inv-equiv e))))
              ( eq-is-prop
                ( is-prop-type-Decidable-Prop (pr1 Y (pr1 (id d Y)))))))
  abstract
    preserves-id-equiv-orientation-complete-undirected-graph-equiv :
      (X : Type-With-Cardinality-ℕ l n) →
      orientation-complete-undirected-graph-equiv X X id-equiv ＝ id-equiv
    preserves-id-equiv-orientation-complete-undirected-graph-equiv X =
      eq-htpy-equiv
        ( λ d →
          eq-htpy
            ( λ Y →
              eq-pair-Σ
                ( ap
                  ( pr1 ∘ d)
                  ( eq-pair-eq-fiber (eq-is-prop is-prop-type-trunc-Prop)))
                ( eq-is-prop
                  ( is-prop-type-Decidable-Prop
                    ( pr1 Y (pr1 (map-equiv id-equiv d Y)))))))
    preserves-comp-orientation-complete-undirected-graph-equiv :
      ( X Y Z : Type-With-Cardinality-ℕ l n)
      (e :
        type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n Y) →
      (f :
        type-Type-With-Cardinality-ℕ n Y ≃ type-Type-With-Cardinality-ℕ n Z) →
      Id
        ( orientation-complete-undirected-graph-equiv X Z (f ∘e e))
        ( ( orientation-complete-undirected-graph-equiv Y Z f) ∘e
          ( orientation-complete-undirected-graph-equiv X Y e))
    preserves-comp-orientation-complete-undirected-graph-equiv X Y Z e f =
      eq-htpy-equiv
        ( λ d →
          eq-htpy
            ( λ S →
              eq-pair-Σ
                ( ap
                  ( λ S' → map-equiv (f ∘e e) (pr1 (d S')))
                  ( htpy-eq
                    ( preserves-comp-precomp-equiv-2-Element-Decidable-Subtype
                        e f)
                    ( S)))
                ( eq-is-prop
                  ( is-prop-type-Decidable-Prop
                    ( pr1 S
                      ( pr1
                        ( map-equiv
                          ( orientation-complete-undirected-graph-equiv Y Z f ∘e
                            orientation-complete-undirected-graph-equiv X Y e)
                          ( d)
                          ( S))))))))
    preserves-even-difference-orientation-complete-undirected-graph-equiv :
      ( X X' : Type-With-Cardinality-ℕ l n)
      ( e :
        type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
      ( d d' : orientation-Complete-Undirected-Graph n X) →
      ( sim-equivalence-relation
        ( even-difference-orientation-Complete-Undirected-Graph n X)
        ( d)
        ( d') ↔
        sim-equivalence-relation
          ( even-difference-orientation-Complete-Undirected-Graph n X')
          ( map-orientation-complete-undirected-graph-equiv X X' e d)
          ( map-orientation-complete-undirected-graph-equiv X X' e d'))
    pr1
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv
          X X' e d d') =
      _∙ ap
          ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
          ( all-elements-equal-has-finite-cardinality
            ( has-finite-cardinality-is-finite
              ( is-finite-subtype-pointwise-difference n X d d'))
            ( pair
              ( number-of-elements-is-finite
                ( is-finite-subtype-pointwise-difference n X'
                  ( map-orientation-complete-undirected-graph-equiv X X' e d)
                  ( map-orientation-complete-undirected-graph-equiv X X' e d')))
              ( map-trunc-Prop
                ( equiv-subtype-pointwise-difference-equiv ∘e_)
                ( pr2
                  ( has-finite-cardinality-is-finite
                    ( is-finite-subtype-pointwise-difference n X'
                      ( map-orientation-complete-undirected-graph-equiv
                          X X' e d)
                      ( map-orientation-complete-undirected-graph-equiv
                          X X' e d')))))))
      where
      equiv-subtype-pointwise-difference-equiv :
        Σ ( 2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X'))
          ( λ Y →
            type-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference n X'
                ( map-orientation-complete-undirected-graph-equiv X X' e d)
                ( map-orientation-complete-undirected-graph-equiv X X' e d')
                ( Y))) ≃
        Σ ( 2-Element-Decidable-Subtype l
            ( type-Type-With-Cardinality-ℕ n X))
          ( λ Y →
            type-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                  n X d d' Y))
      pr1 (pr1 equiv-subtype-pointwise-difference-equiv (pair Y NQ)) =
        precomp-equiv-2-Element-Decidable-Subtype e Y
      pr2 (pr1 equiv-subtype-pointwise-difference-equiv (pair Y NQ)) p =
        NQ
          ( eq-pair-Σ
            ( ap (map-equiv e) (pr1 (pair-eq-Σ p)))
            ( eq-is-prop
              ( is-prop-type-Decidable-Prop
                ( pr1
                  ( Y)
                  ( pr1
                    ( map-orientation-complete-undirected-graph-equiv
                        X X' e d' Y))))))
      pr2 equiv-subtype-pointwise-difference-equiv =
        is-equiv-is-invertible
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
                          ( inv (left-inverse-law-equiv e)))
                        ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( ( is-injective-equiv e (pr1 (pair-eq-Σ p))) ∙
                        ( ap
                          ( λ Y' → pr1 (d' Y'))
                          ( eq-pair-Σ
                            ( ap
                              ( λ h → pr1 Y ∘ map-equiv h)
                              ( left-inverse-law-equiv e))
                            ( eq-is-prop is-prop-type-trunc-Prop)))))
                    ( eq-is-prop
                      ( is-prop-type-Decidable-Prop (pr1 Y (pr1 (d' Y))))))))
          ( λ (pair Y NQ) →
            eq-pair-Σ
              ( eq-pair-Σ
                ( ap (λ h → pr1 Y ∘ map-equiv h) (left-inverse-law-equiv e))
                ( eq-is-prop is-prop-type-trunc-Prop))
              ( eq-is-prop
                ( is-prop-type-Decidable-Prop
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                      n X d d' Y))))
          ( λ (pair Y NQ) →
            eq-pair-Σ
              ( eq-pair-Σ
                ( ap (λ h → pr1 Y ∘ map-equiv h) (right-inverse-law-equiv e))
                ( eq-is-prop is-prop-type-trunc-Prop))
              ( eq-is-prop
                ( is-prop-type-Decidable-Prop
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                    ( n)
                    ( X')
                    ( map-orientation-complete-undirected-graph-equiv X X' e d)
                    ( map-orientation-complete-undirected-graph-equiv X X' e d')
                    ( Y)))))
    pr2
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv
          X X' e d d')
      P =
      tr
        ( λ g →
          sim-equivalence-relation
            ( even-difference-orientation-Complete-Undirected-Graph n X)
            ( map-equiv g d)
            ( map-equiv g d'))
        { x =
          orientation-complete-undirected-graph-equiv X' X (inv-equiv e) ∘e
          orientation-complete-undirected-graph-equiv X X' e}
        { y = id-equiv}
        ( ( inv
            ( preserves-comp-orientation-complete-undirected-graph-equiv
                X X' X e (inv-equiv e))) ∙
          ( ( ap
              ( orientation-complete-undirected-graph-equiv X X)
              ( left-inverse-law-equiv e)) ∙
            ( preserves-id-equiv-orientation-complete-undirected-graph-equiv
              ( X))))
        ( pr1
          ( preserves-even-difference-orientation-complete-undirected-graph-equiv
            ( X')
            ( X)
            ( inv-equiv e)
            ( map-orientation-complete-undirected-graph-equiv X X' e d)
            ( map-orientation-complete-undirected-graph-equiv X X' e d'))
          ( P))
```

</details>

```agda
module _
  {l : Level} {X : UU l}
  (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  cases-orientation-aut-count :
    (e : X ≃ X)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y →
          Σ (x ≠ y)
          ( λ np →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))
              ( Y))))) →
    is-decidable
      ( Id (map-equiv e (pr1 two-elements)) (pr1 two-elements)) →
    is-decidable
      ( Id (map-equiv e (pr1 (pr2 two-elements))) (pr1 (pr2 two-elements))) →
    Σ X (λ z → type-Decidable-Prop (pr1 Y z))
  cases-orientation-aut-count
    e Y (pair x (pair y (pair np P))) (inl q) r =
    pair x (tr (λ Z → type-Decidable-Prop (pr1 Z x)) P (inl refl))
  cases-orientation-aut-count
    e Y (pair x (pair y (pair np P))) (inr nq) (inl nr) =
    pair y (tr (λ Z → type-Decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-aut-count
    e Y (pair x (pair y (pair np P))) (inr nq) (inr nr) =
    pair x (tr (λ Z → type-Decidable-Prop (pr1 Z x)) P (inl refl))

  orientation-aut-count :
    X ≃ X →
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

  cases-orientation-two-elements-count :
    ( i j : X)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements : Σ X
      ( λ x → Σ X
        ( λ y →
          Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    is-decidable (pr1 two-elements ＝ i) →
    is-decidable (pr1 two-elements ＝ j) →
    is-decidable (pr1 (pr2 two-elements) ＝ i) →
    Σ X (λ z → type-Decidable-Prop (pr1 Y z))
  cases-orientation-two-elements-count
    i j Y (pair x (pair y (pair np' P))) (inl q) r s =
    pair y (tr (λ Z → type-Decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-two-elements-count
    i j Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inl s) =
    pair x (tr (λ Z → type-Decidable-Prop (pr1 Z x)) P (inl refl))
  cases-orientation-two-elements-count
    i j Y (pair x (pair y (pair np' P))) (inr nq) (inl r) (inr ns) =
    pair y (tr (λ Z → type-Decidable-Prop (pr1 Z y)) P (inr refl))
  cases-orientation-two-elements-count
    i j Y (pair x (pair y (pair np' P))) (inr nq) (inr nr) s =
    pair x (tr (λ Z → type-Decidable-Prop (pr1 Z x)) P (inl refl))

  orientation-two-elements-count :
    (i j : X) → i ≠ j →
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
    distinct-two-elements-count :
      first-element-count ≠ second-element-count
    distinct-two-elements-count p =
      pr2
        ( pr2
          ( two-distinct-elements-leq-2-Fin
            ( number-of-elements-count eX)
            ( ineq)))
        ( is-injective-equiv (equiv-count eX) p)

  canonical-2-Element-Decidable-Subtype-count :
    2-Element-Decidable-Subtype l X
  canonical-2-Element-Decidable-Subtype-count =
    standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-count eX)
      ( distinct-two-elements-count)

  canonical-orientation-count :
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  canonical-orientation-count =
    orientation-two-elements-count
      ( first-element-count)
      ( second-element-count)
      ( distinct-two-elements-count)

  transitive-canonical-orientation-count :
    orientation-Complete-Undirected-Graph
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))
  transitive-canonical-orientation-count =
    orientation-two-elements-count
      ( second-element-count)
      ( first-element-count)
      ( λ p → distinct-two-elements-count (inv p))

  abstract
    cases-inward-edge-left-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i)) +
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
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))))
        { x =
          pair
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( i))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( j))}
        { y = pair (inr (λ p → nq (inv r1 ∙ p))) (inr (λ p → nr (inv r1 ∙ p)))}
        ( eq-pair-Σ
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
        ( r1)
    cases-inward-edge-left-two-elements-orientation-count
      i j np Y x nq nr (inr (pair r1 r2)) =
      ( ap
        ( λ d →
          pr1
            ( cases-orientation-two-elements-count i j Y
              ( two-elements-transposition eX Y)
              ( d)
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (two-elements-transposition eX Y))
                ( j))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))))
        { x =
          has-decidable-equality-count
            ( eX)
            ( pr1 (two-elements-transposition eX Y))
            ( i)}
        { y = inl r1}
        ( eq-is-prop
          ( is-prop-is-decidable
            ( is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))) ∙
      ( r2)

    inward-edge-left-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y i)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-left-two-elements-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-left-two-elements-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x i nq p1 p2)

    cases-inward-edge-left-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) i)) +
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
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y i)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1
          ( orientation-aut-count
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np)))
            ( Y)))
        ( x)
    inward-edge-left-transposition-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-left-transposition-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x i nq p1 p2)

    cases-inward-edge-right-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j)) +
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
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))))
        { x =
          pair
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( i))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( j))}
        { y = pair (inr (λ p → nq (inv r1 ∙ p))) (inr (λ p → nr (inv r1 ∙ p)))}
        ( eq-pair-Σ
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
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
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))))
        { x =
          pair
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( i))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( j))}
        { y = pair (inr λ p → np (inv p ∙ r1)) (inl r1)}
        ( eq-pair-Σ
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) i)))
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count eX (pr1 (two-elements-transposition eX Y)) j))))) ∙
        ( ( ap
          ( λ d →
            pr1
              ( cases-orientation-two-elements-count i j Y
                ( two-elements-transposition eX Y)
                ( inr λ p → np (inv p ∙ r1))
                ( inl r1)
                ( d)))
          { x =
            has-decidable-equality-count
              ( eX)
              ( pr1 (pr2 (two-elements-transposition eX Y)))
              ( i)}
          { y = inr (λ q → nq (inv r2 ∙ q))}
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-set-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))))) ∙
          ( r2))

    inward-edge-right-two-elements-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y j)) →
      x ≠ i → x ≠ j →
      Id
        ( pr1 (orientation-two-elements-count i j np Y))
        ( x)
    inward-edge-right-two-elements-orientation-count i j np Y x p1 p2 nq nr =
      cases-inward-edge-right-two-elements-orientation-count i j np Y x nq nr
        ( eq-two-elements-transposition eX Y x j nr p1 p2)

    cases-inward-edge-right-transposition-orientation-count :
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      x ≠ i → x ≠ j →
      ( ( Id (pr1 (two-elements-transposition eX Y)) x) ×
        ( Id (pr1 (pr2 (two-elements-transposition eX Y))) j)) +
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
      (i j : X) (np : i ≠ j)
      (Y : 2-Element-Decidable-Subtype l X) (x : X) →
      ( type-Decidable-Prop (pr1 Y x)) →
      ( type-Decidable-Prop (pr1 Y j)) →
      x ≠ i → x ≠ j →
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

    cases-eq-orientation-two-elements-count :
      ( i j : X)
      ( np : i ≠ j)
      ( two-elements : Σ X
        ( λ x → Σ X
          ( λ y → Σ (x ≠ y)
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))))) →
      (q : is-decidable (pr1 two-elements ＝ i)) →
      (r : is-decidable (pr1 two-elements ＝ j)) →
      (s : is-decidable (pr1 (pr2 two-elements) ＝ i)) →
      (t : is-decidable (pr1 (pr2 two-elements) ＝ j)) →
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
            ( left-computation-standard-transposition
              ( has-decidable-equality-count eX)
              ( np'))) ∙
            ( ( ap
              ( map-standard-transposition
                ( has-decidable-equality-count eX)
                ( np'))
              ( q)) ∙
              ( ( ap (λ Y → map-transposition Y i) P) ∙
                ( left-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np))))))
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inr nq) (inl r) (inl s) t = r
    cases-eq-orientation-two-elements-count
      i j np (pair x (pair y (pair np' P))) (inr nq) (inl r) (inr ns) t =
      ex-falso
        ( ns
          ( ( inv
              ( left-computation-standard-transposition
                ( has-decidable-equality-count eX)
                ( np'))) ∙
            ( ( ap
                ( map-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( r)) ∙
              ( ( ap (λ Y → map-transposition Y j) P) ∙
                ( right-computation-standard-transposition
                  ( has-decidable-equality-count eX)
                  ( np))))))
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
            (tr (λ Y → type-Decidable-Prop (pr1 Y x)) P (inl refl)))
          ( λ eq → np (pr1 (pair-eq-Σ eq)))
          ( λ eq → nr (inv (pr1 (pair-eq-Σ eq))))
          ( λ eq → nq (inv (pr1 (pair-eq-Σ eq)))))

    eq-orientation-two-elements-count :
      (i j : X) (np : i ≠ j) →
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
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np)))
        ( has-decidable-equality-count eX
          ( pr1
            ( two-elements-transposition eX
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))))
          ( i))
        ( has-decidable-equality-count eX
          ( pr1
          ( two-elements-transposition eX
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np))))
          ( j))
        ( has-decidable-equality-count eX
          ( pr1
          ( pr2
            ( two-elements-transposition eX
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))))
          ( i))
        ( has-decidable-equality-count eX
          ( pr1
            ( pr2
              ( two-elements-transposition eX
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np)))))
          ( j))

  cases-eq-orientation-aut-orientation-two-elements-count-left :
    ( i j : X) (np : i ≠ j) →
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
        ( λ y → Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    two-elements-transposition eX Y ＝ two-elements →
    is-decidable (pr1 two-elements ＝ i) →
    is-decidable (pr1 two-elements ＝ j) →
    is-decidable (pr1 (pr2 two-elements) ＝ i) →
    is-decidable (pr1 (pr2 two-elements) ＝ j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
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
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inl q))
      ( λ s' → np' (q ∙ inv s'))
      ( nt)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count i j np Y y
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inl q))
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
            ( eq-equal-elements-standard-2-Element-Decidable-Subtype
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
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inl r))
      ( ns)
      ( λ t' → np' (r ∙ inv t'))) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count i j np Y y
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inl r))
          ( ns)
          ( λ t' → np' (r ∙ inv t'))))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inl s) t =
    ( inward-edge-left-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inr s))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count i j np Y x
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inr s))
          ( nq)
          ( nr)))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inl t) =
    ( inward-edge-right-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inr t))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count i j np Y x
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inr t))
          ( nq)
          ( nr)))
  cases-eq-orientation-aut-orientation-two-elements-count-left
    i j np Q Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inr nt) =
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
    ( i j : X) (np : i ≠ j) →
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
        ( λ y → Σ (x ≠ y)
          ( λ np' →
            Id
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np'))
              ( Y))))) →
    two-elements-transposition eX Y ＝ two-elements →
    is-decidable (pr1 two-elements ＝ i) →
    is-decidable (pr1 two-elements ＝ j) →
    is-decidable (pr1 (pr2 two-elements) ＝ i) →
    is-decidable (pr1 (pr2 two-elements) ＝ j) →
    Id
      ( pr1
        ( orientation-aut-count
          ( transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np)))
          ( Y)))
      ( pr1 (orientation-two-elements-count j i (np ∘ inv) Y))
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
        ( ( inv (eq-orientation-two-elements-count j i (np ∘ inv))) ∙
          ( ap
            ( pr1 ∘ orientation-two-elements-count j i (np ∘ inv))
            ( ( is-commutative-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np ∘ inv)) ∙
              ( ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( λ p → np (inv (inv p)))
                ( np')
                ( inv q)
                ( inv t)) ∙
                ( P))))))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inl q) r s (inr nt) =
    ( inward-edge-left-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inl q))
      ( λ s' → np' (q ∙ inv s'))
      ( nt)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count
          ( j)
          ( i)
          ( np ∘ inv)
          ( Y)
          ( y)
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inl q))
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
        ( ( inv (eq-orientation-two-elements-count j i (np ∘ inv))) ∙
          ( ap
            ( pr1 ∘ orientation-two-elements-count j i (np ∘ inv))
            ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np ∘ inv)
                ( np')
                ( inv r)
                ( inv s) ∙
                ( P)))))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inl r) (inr ns) t =
    ( inward-edge-right-transposition-orientation-count i j np Y y
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inl r))
      ( ns)
      ( λ t' → np' (r ∙ inv t'))) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count
          ( j)
          ( i)
          ( np ∘ inv)
          ( Y)
          ( y)
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inl r))
          ( λ t' → np' (r ∙ inv t'))
          ( ns)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P))) R (inr nq) (inr nr) (inl s) t =
    ( inward-edge-left-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inr s))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-right-two-elements-orientation-count
          ( j)
          ( i)
          ( np ∘ inv)
          ( Y)
          ( x)
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inr s))
          ( nr)
          ( nq)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inl t) =
    ( inward-edge-right-transposition-orientation-count i j np Y x
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
      ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inr t))
      ( nq)
      ( nr)) ∙
      ( inv
        ( inward-edge-left-two-elements-orientation-count
          ( j)
          ( i)
          ( np ∘ inv)
          ( Y)
          ( x)
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inr t))
          ( nr)
          ( nq)))
  cases-eq-orientation-aut-orientation-two-elements-count-right
    i j np Q Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inr nt) =
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
    ( i j : X) (np : i ≠ j) →
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
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv)))
  cases-eq-orientation-aut-orientation-two-elements-count i j np (inl q) =
    inl
      ( eq-htpy
        ( λ Y →
          eq-pair-Σ
            ( cases-eq-orientation-aut-orientation-two-elements-count-left
              ( i)
              ( j)
              ( np)
              ( q)
              ( Y)
              ( two-elements-transposition eX Y)
              ( refl)
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (two-elements-transposition eX Y))
                ( i))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (two-elements-transposition eX Y))
                ( j))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( j)))
            ( eq-is-prop
              ( is-prop-type-Decidable-Prop
                ( pr1 Y (pr1 (orientation-two-elements-count i j np Y)))))))
  cases-eq-orientation-aut-orientation-two-elements-count i j np (inr nq) =
    inr
      ( eq-htpy
        ( λ Y →
          eq-pair-Σ
            ( cases-eq-orientation-aut-orientation-two-elements-count-right
              ( i)
              ( j)
              ( np)
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
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (two-elements-transposition eX Y))
                ( i))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (two-elements-transposition eX Y))
                ( j))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( i))
              ( has-decidable-equality-count
                ( eX)
                ( pr1 (pr2 (two-elements-transposition eX Y)))
                ( j)))
            ( eq-is-prop
              ( is-prop-type-Decidable-Prop
                ( pr1
                  ( Y)
                  ( pr1
                    ( orientation-two-elements-count
                        j i (np ∘ inv) Y)))))))
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
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
              ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv)))
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
    ( i j : X) (np : i ≠ j)
    ( Y : 2-Element-Decidable-Subtype l X)
    ( two-elements :
      Σ X
        ( λ x → Σ X
          ( λ y → Σ (x ≠ y)
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( Y))))) →
    two-elements-transposition eX Y ＝ two-elements →
    is-decidable (pr1 two-elements ＝ i) →
    is-decidable (pr1 two-elements ＝ j) →
    is-decidable (pr1 (pr2 two-elements) ＝ i) →
    is-decidable (pr1 (pr2 two-elements) ＝ j) →
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
      ( pr1 ( orientation-two-elements-count j i (np ∘ inv) Y))
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
          ( ( right-computation-standard-transposition
              ( has-decidable-equality-count eX)
              ( np)) ∙
            ( inv (eq-orientation-two-elements-count j i (np ∘ inv)) ∙
              ( ap
              ( λ Y' → pr1 (orientation-two-elements-count j i (np ∘ inv) Y'))
              ( ( is-commutative-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np ∘ inv)) ∙
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
            type-Decidable-Prop
              ( ( pr1 Y'
                  ( map-inv-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( y)))))
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
            type-Decidable-Prop
              ( pr1 Y'
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( j))))
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
          ( inward-edge-right-two-elements-orientation-count j i (np ∘ inv) Y y
            ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
            ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inl q))
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
          ( ( right-computation-standard-transposition
              ( has-decidable-equality-count eX)
              ( np)) ∙
            ( ( inv (eq-orientation-two-elements-count j i (np ∘ inv))) ∙
              ( ap
                ( pr1 ∘ orientation-two-elements-count j i (np ∘ inv))
                ( eq-equal-elements-standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np ∘ inv)
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
              type-Decidable-Prop
                ( pr1 Y'
                  ( map-inv-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( y))))
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
              type-Decidable-Prop
                ( pr1 Y'
                  ( map-inv-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( i))))
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
            ( inward-edge-left-two-elements-orientation-count j i (np ∘ inv) Y y
              ( tr (λ Y' → type-Decidable-Prop (pr1 Y' y)) P (inr refl))
              ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inl r))
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
              type-Decidable-Prop
                ( pr1 Y'
                    ( map-inv-equiv
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-count eX)
                          ( np)))
                      ( x))))
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
              type-Decidable-Prop
                ( pr1 Y'
                  ( map-inv-equiv
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-count eX)
                        ( np)))
                    ( j))))
            ( P)
            ( inr
              ( s ∙
                ( inv
                  ( right-computation-standard-transposition
                    ( has-decidable-equality-count eX)
                    ( np))))))
          ( nq)
          ( nr)) ∙
        ( is-fixed-point-standard-transposition
          ( has-decidable-equality-count eX)
          ( np)
          ( x)
          ( λ q → nq (inv q))
          ( λ r → nr (inv r)) ∙
          ( inv
            ( inward-edge-right-two-elements-orientation-count
              j i (np ∘ inv) Y x
              ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
              ( tr (λ Y' → type-Decidable-Prop (pr1 Y' i)) P (inr s))
              ( nr)
              ( nq))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inl t) =
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
            type-Decidable-Prop
              ( pr1 Y'
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( x))))
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
            type-Decidable-Prop
              ( pr1 Y'
                ( map-inv-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count eX)
                      ( np)))
                  ( i))))
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
        ( inward-edge-left-two-elements-orientation-count j i (np ∘ inv) Y x
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' x)) P (inl refl))
          ( tr (λ Y' → type-Decidable-Prop (pr1 Y' j)) P (inr t))
          ( nr)
          ( nq))))
  cases-eq-map-orientation-transposition-orientation-two-elements-count
    i j np Y (pair x (pair y (pair np' P)))
    R (inr nq) (inr nr) (inr ns) (inr nt) =
    ( ap
      ( map-inv-equiv
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( ( ap
          ( λ Y' → pr1 (orientation-two-elements-count i j np Y'))
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
    ( i j : X) (np : i ≠ j) →
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
      ( orientation-two-elements-count j i (np ∘ inv))
  eq-map-orientation-transposition-orientation-two-elements-count i j np =
    eq-htpy
      ( λ Y →
        eq-pair-Σ
          ( cases-eq-map-orientation-transposition-orientation-two-elements-count
            ( i)
            ( j)
            ( np)
            ( Y)
            ( two-elements-transposition eX Y)
            ( refl)
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( i))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (two-elements-transposition eX Y))
              ( j))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (pr2 (two-elements-transposition eX Y)))
              ( i))
            ( has-decidable-equality-count
              ( eX)
              ( pr1 (pr2 (two-elements-transposition eX Y)))
              ( j)))
          ( eq-is-prop
            ( is-prop-type-Decidable-Prop
              ( pr1 Y
                ( pr1 (orientation-two-elements-count j i (np ∘ inv) Y))))))

  equiv-fin-1-difference-orientation-two-elements-count :
    ( i j : X) (np : i ≠ j) →
    Fin 1 ≃
    Σ ( 2-Element-Decidable-Subtype l X)
      ( λ Y → type-Decidable-Prop
        ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( orientation-two-elements-count i j np)
          ( orientation-two-elements-count j i (np ∘ inv))
          ( Y)))
  pr1 (pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np) x) =
    standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np
  pr2 (pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np) x) q =
    np
      ( ( inv (eq-orientation-two-elements-count j i (np ∘ inv))) ∙
        ( ( ap
            ( λ Y → pr1 (orientation-two-elements-count j i (np ∘ inv) Y))
            { x =
              standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np ∘ inv)}
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
    is-equiv-is-invertible
      ( λ x → inr star)
      ( λ T →
        eq-pair-Σ
          ( retraction-fin-1-difference-orientation-two-elements-count
            ( T)
            ( two-elements-transposition eX (pr1 T))
            ( refl)
            ( has-decidable-equality-count
              (eX) (pr1 (two-elements-transposition eX (pr1 T))) (i))
            ( has-decidable-equality-count
              (eX) (pr1 (two-elements-transposition eX (pr1 T))) (j))
            ( has-decidable-equality-count
              (eX) (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) (i))
            ( has-decidable-equality-count
              (eX) (pr1 (pr2 (two-elements-transposition eX (pr1 T)))) (j)))
          ( eq-is-prop
            ( is-prop-type-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( orientation-two-elements-count i j np)
                ( orientation-two-elements-count j i (np ∘ inv))
                ( pr1 T)))))
      ( section-fin-1-difference-orientation-two-elements-count)
    where
    retraction-fin-1-difference-orientation-two-elements-count :
      ( T :
        Σ ( 2-Element-Decidable-Subtype l X)
          ( λ Y →
            type-Decidable-Prop
              ( 2-Element-Decidable-Subtype-subtype-pointwise-difference
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( orientation-two-elements-count i j np)
                ( orientation-two-elements-count j i (np ∘ inv))
                ( Y)))) →
      ( two-elements : Σ X
        ( λ x → Σ X
          ( λ y → Σ (x ≠ y)
            ( λ np' →
              Id
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-count eX)
                  ( np'))
                ( pr1 T))))) →
      Id two-elements (two-elements-transposition eX (pr1 T)) →
      is-decidable (pr1 two-elements ＝ i) →
      is-decidable (pr1 two-elements ＝ j) →
      is-decidable (pr1 (pr2 two-elements) ＝ i) →
      is-decidable (pr1 (pr2 two-elements) ＝ j) →
      Id
        ( standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-count eX)
          ( np))
        ( pr1 T)
    retraction-fin-1-difference-orientation-two-elements-count
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
    retraction-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inl q) r s (inr nt) =
      ex-falso
        ( pr2 T
          ( eq-pair-Σ
            ( ( inward-edge-left-two-elements-orientation-count i j np
                ( pr1 T)
                ( y)
                ( tr
                  ( λ Y → type-Decidable-Prop (pr1 Y y))
                  ( P)
                  ( inr refl))
                ( tr
                  ( λ z → type-Decidable-Prop (pr1 (pr1 T) z))
                  ( q)
                  ( tr
                    ( λ Y → type-Decidable-Prop (pr1 Y x))
                    ( P)
                    ( inl refl)))
                ( λ s → np' (q ∙ inv s))
                ( nt)) ∙
              ( inv
                ( inward-edge-right-two-elements-orientation-count j i
                  ( np ∘ inv)
                  ( pr1 T)
                  ( y)
                  ( tr
                    ( λ Y → type-Decidable-Prop (pr1 Y y))
                    ( P)
                    ( inr refl))
                  ( tr
                    ( λ z → type-Decidable-Prop (pr1 (pr1 T) z))
                    ( q)
                    ( tr
                      ( λ Y → type-Decidable-Prop (pr1 Y x))
                      ( P)
                      ( inl refl)))
                  ( nt)
                  ( λ s → np' (q ∙ inv s)))))
            ( eq-is-prop
              ( is-prop-type-Decidable-Prop
                ( pr1
                  ( pr1 T)
                  ( pr1
                    ( orientation-two-elements-count
                        j i (np ∘ inv) (pr1 T))))))))
    retraction-fin-1-difference-orientation-two-elements-count
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
          ( inv
            ( is-commutative-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( np')) ∙
            ( P)))
    retraction-fin-1-difference-orientation-two-elements-count
      T (pair x (pair y (pair np' P))) Q (inr nq) (inl r) (inr ns) t =
      ex-falso
        ( pr2 T
          ( eq-pair-Σ
            ( inward-edge-right-two-elements-orientation-count i j np
              ( pr1 T)
              ( y)
              ( tr
                ( λ Y → type-Decidable-Prop (pr1 Y y))
                ( P)
                ( inr refl))
              ( tr
                ( λ z → type-Decidable-Prop (pr1 (pr1 T) z))
                ( r)
                ( tr
                  ( λ Y → type-Decidable-Prop (pr1 Y x))
                  ( P)
                  ( inl refl)))
              ( ns)
              ( λ t → np' (r ∙ inv t)) ∙
              ( inv
                ( inward-edge-left-two-elements-orientation-count j i
                  ( np ∘ inv)
                  ( pr1 T)
                  ( y)
                  ( tr
                    ( λ Y → type-Decidable-Prop (pr1 Y y))
                    ( P)
                    ( inr refl))
                  ( tr
                    ( λ z → type-Decidable-Prop (pr1 (pr1 T) z))
                    ( r)
                    ( tr
                      ( λ Y → type-Decidable-Prop (pr1 Y x))
                      ( P)
                      ( inl refl)))
                  ( λ t → np' (r ∙ inv t))
                  ( ns))))
            ( eq-is-prop
              ( is-prop-type-Decidable-Prop
                ( pr1
                  ( pr1 T)
                  ( pr1
                    ( orientation-two-elements-count
                        j i (np ∘ inv) (pr1 T))))))))
    retraction-fin-1-difference-orientation-two-elements-count
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
                    ( pair x (pair y (pair np' P)))
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
    section-fin-1-difference-orientation-two-elements-count :
      ( ( λ x → inr {A = empty} star) ∘
        pr1 (equiv-fin-1-difference-orientation-two-elements-count i j np)) ~
      ( id)
    section-fin-1-difference-orientation-two-elements-count (inr star) = refl

  eq-orientation-pointwise-difference-two-elements-count :
    (i j : X) (np : i ≠ j) →
    Id
      ( 1)
      ( number-of-elements-is-finite
        ( is-finite-subtype-pointwise-difference
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( orientation-two-elements-count i j np)
          ( orientation-two-elements-count j i (np ∘ inv))))
  eq-orientation-pointwise-difference-two-elements-count i j np =
    ap
      ( number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair
          ( 1)
          ( unit-trunc-Prop
            ( equiv-fin-1-difference-orientation-two-elements-count i j np)))
        ( has-finite-cardinality-is-finite
          ( is-finite-subtype-pointwise-difference
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( orientation-two-elements-count i j np)
            ( orientation-two-elements-count j i (np ∘ inv)))))

  cases-not-even-difference-orientation-aut-transposition-count :
    ( i j : X) (np : i ≠ j) →
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count i j np)) +
    ( Id
      ( orientation-aut-count
        ( transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-count eX)
            ( np))))
      ( orientation-two-elements-count j i (np ∘ inv))) →
    ¬ ( sim-equivalence-relation
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
  cases-not-even-difference-orientation-aut-transposition-count
    i j np (inl pl) =
    tr
      ( λ d →
        ¬ ( sim-equivalence-relation
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
          ¬ ( sim-equivalence-relation
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( orientation-two-elements-count i j np)
            ( d)))
        ( inv
          ( eq-map-orientation-transposition-orientation-two-elements-count
              i j np))
        ( λ p →
          neq-inl-inr
            ( p ∙
              ( inv
                ( ap mod-two-ℕ
                  ( eq-orientation-pointwise-difference-two-elements-count
                      i j np))))))
  cases-not-even-difference-orientation-aut-transposition-count
    i j np (inr pr) =
    tr
      ( λ d →
        ¬ ( sim-equivalence-relation
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
          ¬ ( sim-equivalence-relation
              ( even-difference-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( orientation-two-elements-count j i (np ∘ inv))
              ( d)))
        ( inv
          ( ( ap
              ( λ w →
                map-orientation-complete-undirected-graph-equiv
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( transposition w)
                  ( orientation-two-elements-count j i (np ∘ inv)))
              ( is-commutative-standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-count eX)
                ( np))) ∙
            ( eq-map-orientation-transposition-orientation-two-elements-count
                j i (np ∘ inv))))
        ( λ p →
          neq-inl-inr
            ( p ∙
              ( inv
                ( ap
                  ( mod-two-ℕ)
                  ( eq-orientation-pointwise-difference-two-elements-count j i
                    ( np ∘ inv)))))))

  not-even-difference-orientation-aut-transposition-count :
    ( Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( sim-equivalence-relation
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
        ¬ ( sim-equivalence-relation
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
    ( T :
      quotient-sign
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( is-in-equivalence-class
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( canonical-orientation-count)) →
    Fin 2
  inv-orientation T (inl P) = inl (inr star)
  inv-orientation T (inr NP) = inr star

  equiv-fin-2-quotient-sign-count :
    Fin 2 ≃
    ( quotient-sign
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX))))
  pr1 equiv-fin-2-quotient-sign-count (inl (inr star)) =
    class
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( canonical-orientation-count)
  pr1 equiv-fin-2-quotient-sign-count (inr star) =
    class
      ( even-difference-orientation-Complete-Undirected-Graph
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( transitive-canonical-orientation-count)
  pr2 equiv-fin-2-quotient-sign-count =
    is-equiv-is-invertible
      ( λ T →
        inv-orientation
          ( T)
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count)))
      ( λ T →
        retraction-orientation
          ( T)
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count)))
      ( λ k →
        section-orientation
          k
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( pr1 equiv-fin-2-quotient-sign-count k)
            ( canonical-orientation-count)))
    where
    cases-retraction-orientation :
      (T :
        equivalence-class
          ( even-difference-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))) →
      ¬ ( is-in-equivalence-class
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
        ( class
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
      is-in-equivalence-class
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( transitive-canonical-orientation-count)
    cases-retraction-orientation T NH t q (inl (inr star)) r =
      ex-falso
        ( NH
          ( tr
            ( λ x →
              is-in-equivalence-class
                ( even-difference-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( x)
                ( canonical-orientation-count))
            ( q)
            ( r)))
    cases-retraction-orientation T NH t q (inr star) r =
      tr
        (λ x →
          is-in-equivalence-class
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( x)
            ( transitive-canonical-orientation-count))
        ( q)
        ( eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( t)
            ( canonical-orientation-count)
            ( transitive-canonical-orientation-count)
            ( inr star)
            ( r)
            ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( transitive-canonical-orientation-count)
              ( canonical-orientation-count)
              ( inr star)
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( canonical-orientation-count)
                ( transitive-canonical-orientation-count)
                ( inr star)
                ( ap
                  ( mod-two-ℕ)
                  { x = 1}
                  { y =
                    number-of-elements-is-finite
                      ( is-finite-subtype-pointwise-difference
                        ( number-of-elements-count eX)
                        ( pair X (unit-trunc-Prop (equiv-count eX)))
                        ( canonical-orientation-count)
                        ( transitive-canonical-orientation-count))}
                  ( eq-orientation-pointwise-difference-two-elements-count
                    ( first-element-count)
                    ( second-element-count)
                    ( distinct-two-elements-count))))))
    retraction-orientation :
      ( T :
        quotient-sign
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ( H :
        is-decidable
          (is-in-equivalence-class
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( T)
            ( canonical-orientation-count))) →
      Id (pr1 equiv-fin-2-quotient-sign-count (inv-orientation T H)) T
    retraction-orientation T (inl H) =
      eq-effective-quotient'
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( canonical-orientation-count)
        ( T)
        ( H)
    retraction-orientation T (inr NH) =
      eq-effective-quotient'
        ( even-difference-orientation-Complete-Undirected-Graph
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( transitive-canonical-orientation-count)
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( pair
            ( is-in-equivalence-class
              ( even-difference-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( transitive-canonical-orientation-count))
            ( is-prop-is-in-equivalence-class
              ( even-difference-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( transitive-canonical-orientation-count)))
          ( λ (pair t r) →
            cases-retraction-orientation
              ( T)
              ( NH)
              ( t)
              ( eq-pair-Σ
                ( ap
                  ( pr1)
                  ( inv
                    ( eq-has-same-elements-equivalence-class
                      ( even-difference-orientation-Complete-Undirected-Graph
                        ( number-of-elements-count eX)
                        ( pair X (unit-trunc-Prop (equiv-count eX))))
                      ( T)
                      ( class
                        ( even-difference-orientation-Complete-Undirected-Graph
                          ( number-of-elements-count eX)
                          ( pair X (unit-trunc-Prop (equiv-count eX))))
                        ( t))
                      ( r))))
                ( all-elements-equal-type-trunc-Prop _ (pr2 T)))
              ( mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX)))
                  ( t)
                  ( canonical-orientation-count))
              ( refl)))
    section-orientation :
      (k : Fin 2)
      ( D : is-decidable
        ( is-in-equivalence-class
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
    section-orientation (inl (inr star)) (inl Q) = refl
    section-orientation (inl (inr star)) (inr NQ) =
      ex-falso
        ( NQ
          ( refl-equivalence-relation
            ( even-difference-orientation-Complete-Undirected-Graph
              ( number-of-elements-count eX)
              ( X , (unit-trunc-Prop (equiv-count eX))))
            ( canonical-orientation-count)))
    section-orientation (inr star) (inl Q) =
      ex-falso
        ( neq-inl-inr
          ( Q ∙
            inv
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graph
                ( number-of-elements-count eX)
                ( X , (unit-trunc-Prop (equiv-count eX)))
                ( canonical-orientation-count)
                ( transitive-canonical-orientation-count)
                ( inr star)
                ( ap mod-two-ℕ
                  ( eq-orientation-pointwise-difference-two-elements-count
                    ( first-element-count)
                    ( second-element-count)
                    ( distinct-two-elements-count))))))
    section-orientation (inr star) (inr NQ) = refl

module _
  {l : Level} (n : ℕ) (X : Type-With-Cardinality-ℕ l n) (ineq : leq-ℕ 2 n)
  where

  equiv-fin-2-quotient-sign-equiv-Fin :
    Fin n ≃ type-Type-With-Cardinality-ℕ n X → Fin 2 ≃ quotient-sign n X
  equiv-fin-2-quotient-sign-equiv-Fin h =
    tr
      ( λ e →
        Fin 2 ≃ quotient-sign n (type-Type-With-Cardinality-ℕ n X , e))
      ( all-elements-equal-type-trunc-Prop
        ( unit-trunc-Prop (equiv-count (pair n h)))
        ( pr2 X))
      ( equiv-fin-2-quotient-sign-count (pair n h) ineq)
```
