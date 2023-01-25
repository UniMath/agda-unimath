---
title: Cartier's delooping of the sign homomorphism
---

```agda
{-# OPTIONS --without-K --exact-split --experimental-lossy-unification #-}

module finite-group-theory.cartier-delooping-sign-homomorphism where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import finite-group-theory.delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations using
  ( is-contr-parity-transposition-permutation;
    list-transpositions-permutation-count;
    retr-permutation-list-transpositions-count;
    is-generated-transposition-symmetric-Fin-Level)
open import finite-group-theory.sign-homomorphism using
  ( sign-homomorphism; eq-sign-homomorphism-transposition)
open import finite-group-theory.transpositions using
  ( permutation-list-transpositions; eq-concat-permutation-list-transpositions;
    is-transposition-permutation-Prop; transposition;
    two-elements-transposition; transposition-conjugation-equiv;
    is-involution-map-transposition;
    correct-transposition-conjugation-equiv-list;
    correct-transposition-conjugation-equiv; eq-equiv-universes-transposition)

open import foundation.automorphisms using (Aut)
open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-types using (is-contr; center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr; neq-inr-inl)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop; is-prop-is-decidable)
open import foundation.decidable-types using
  ( is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap-emb; map-emb)
open import foundation.equality-dependent-pair-types using
  ( pair-eq-Σ; eq-pair-Σ; issec-pair-eq-Σ; comp-eq-pair-Σ; ap-pair-eq-Σ; inv-eq-pair-Σ)
open import foundation.equivalence-classes using
  ( equivalence-class; equivalence-class-Set; class;
    eq-effective-quotient';
    quotient-reflecting-map-equivalence-class)
open import foundation.equivalences using
  ( _≃_; _∘e_; map-equiv; inv-equiv; id-equiv; map-inv-equiv;
    inv-inv-equiv; right-inverse-law-equiv; left-inverse-law-equiv;
    distributive-inv-comp-equiv; is-equiv-has-inverse; right-unit-law-equiv;
    is-equiv-map-equiv; associative-comp-equiv)
open import foundation.equivalence-extensionality using
  ( eq-htpy-equiv; htpy-eq-equiv)
open import foundation.equivalence-relations using
  ( Eq-Rel; refl-Eq-Rel; sim-Eq-Rel; is-prop-sim-Eq-Rel)
open import foundation.functions using (_∘_)
open import foundation.function-extensionality using (eq-htpy; htpy-eq)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.functoriality-set-quotients using
  ( unique-equiv-is-set-quotient; equiv-is-set-quotient;
    eq-equiv-eq-one-value-equiv-is-set-quotient)
open import foundation.empty-types using (ex-falso)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using
  ( Id; inv; _∙_; ap; refl; tr; ap-concat; distributive-inv-concat; inv-inv; ap-binary)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.mere-equivalences using
  ( transitive-mere-equiv; symmetric-mere-equiv; mere-equiv; is-set-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop;
    is-prop-type-trunc-Prop; all-elements-equal-type-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel; reflects-map-reflecting-map-Eq-Rel)
open import foundation.raising-universe-levels using
  ( raise-Set; equiv-raise; raise)
open import foundation.sets using
  ( is-set; Id-Prop; Set; type-Set; is-set-type-Set; is-prop-is-set;
    is-set-equiv; is-1-type-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.unit-type using (star)
open import foundation.univalence using
  ( equiv-eq; eq-equiv; comp-eq-equiv; comp-equiv-eq; commutativity-inv-eq-equiv; equiv-univalence)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient-equivalence-class; is-effective-is-set-quotient)
open import foundation.universe-levels using (Level; lzero; lsuc; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using
  ( classifying-type-Concrete-Group; abstract-group-Concrete-Group)
open import group-theory.groups using
  ( set-Group; type-Group; mul-Group; semigroup-Group)
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-generated-subgroups using
  ( restriction-generating-subset-Group;
    eq-map-restriction-generating-subset-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; htpy-hom-Group; comp-hom-Group; map-hom-Group;
    preserves-mul-hom-Group; htpy-eq-hom-Group; id-hom-Group;
    associative-comp-hom-Group)
open import group-theory.homomorphisms-semigroups using
  ( preserves-mul; is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using
  ( hom-iso-Group; hom-inv-iso-Group; comp-iso-Group; inv-iso-Group)
open import group-theory.loop-groups-sets using
  ( loop-group-Set; map-hom-symmetric-group-loop-group-Set;
    hom-symmetric-group-loop-group-Set;
    map-hom-inv-symmetric-group-loop-group-Set;
    hom-inv-symmetric-group-loop-group-Set;
    is-retr-hom-inv-symmetric-group-loop-group-Set;
    is-sec-hom-inv-symmetric-group-loop-group-Set;
    iso-symmetric-group-loop-group-Set;
    commutative-inv-map-hom-symmetric-group-loop-group-Set;
    iso-loop-group-equiv-Set; iso-abstract-automorphism-group-loop-group-Set)
open import group-theory.subgroups using (group-Subgroup)
open import group-theory.subgroups-generated-by-subsets-groups using
  ( is-generating-subset-Group; subgroup-subset-Group)
open import group-theory.symmetric-groups using
  ( symmetric-Group; hom-symmetric-group-equiv-Set;
    hom-inv-symmetric-group-equiv-Set; iso-symmetric-group-equiv-Set)

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; standard-2-Element-Decidable-Subtype;
    equiv-universes-2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-types using
  ( aut-point-Fin-two-ℕ; is-involution-aut-Fin-two-ℕ;
    preserves-add-aut-point-Fin-two-ℕ)
open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; equiv-count; has-decidable-equality-count;
    is-set-count)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin; type-UU-Fin; has-cardinality; set-UU-Fin;
    has-cardinality-type-UU-Fin; Fin-UU-Fin)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list;
    in-list)
open import univalent-combinatorics.orientations-complete-undirected-graph
open import univalent-combinatorics.standard-finite-types
```

## Idea

## Definitions

```agda
module _
  { l : Level}
  where

  cartier-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc l) 2)
  cartier-delooping-sign =
    quotient-delooping-sign
      ( orientation-Complete-Undirected-Graph)
      ( even-difference-orientation-Complete-Undirected-Graph)
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( orientation-complete-undirected-graph-equiv)
      ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( λ n →
        not-even-difference-orientation-aut-transposition-count
          ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))

  eq-cartier-delooping-sign-homomorphism : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc l) 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc l) 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n)))
            ( UU-Fin-Group (lsuc l) 2)
            ( cartier-delooping-sign (succ-ℕ (succ-ℕ n))))
          ( hom-inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l (succ-ℕ (succ-ℕ n)))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc l) 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc l) 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom
            ( orientation-Complete-Undirected-Graph)
            ( even-difference-orientation-Complete-Undirected-Graph)
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
            ( equiv-fin-2-quotient-sign-equiv-Fin)
            ( orientation-complete-undirected-graph-equiv)
            ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
            ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
            ( λ n →
              orientation-aut-count
                ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
            ( λ n →
              not-even-difference-orientation-aut-transposition-count
                ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
            ( n))
          ( sign-homomorphism
            ( succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  eq-cartier-delooping-sign-homomorphism =
    eq-quotient-delooping-sign-homomorphism
      ( orientation-Complete-Undirected-Graph)
      ( even-difference-orientation-Complete-Undirected-Graph)
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph)
      ( equiv-fin-2-quotient-sign-equiv-Fin)
      ( orientation-complete-undirected-graph-equiv)
      ( preserves-id-equiv-orientation-complete-undirected-graph-equiv)
      ( preserves-even-difference-orientation-complete-undirected-graph-equiv)
      ( λ n →
        orientation-aut-count
          ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
      ( λ n →
        not-even-difference-orientation-aut-transposition-count
          ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
```
