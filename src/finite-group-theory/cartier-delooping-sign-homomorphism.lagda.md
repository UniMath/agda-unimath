# The sign homomorphism

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.cartier-delooping-sign-homomorphism where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import finite-group-theory.permutations using
  ( is-contr-parity-transposition-permutation;
    list-transpositions-permutation-count;
    retr-permutation-list-transpositions-count; is-generated-transposition-symmetric-Fin-Level)
open import finite-group-theory.transpositions using
  ( permutation-list-transpositions; eq-concat-permutation-list-transpositions;
    is-transposition-permutation-Prop; transposition; two-elements-transposition;
    transposition-conjugation-equiv; is-involution-map-transposition;
    correct-transposition-conjugation-equiv-list)

open import foundation.automorphisms using (Aut)
open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-types using (center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr; neq-inr-inl)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap-emb; map-emb)
open import foundation.equality-dependent-pair-types using (pair-eq-Σ; eq-pair-Σ)
open import foundation.equivalence-classes using
  ( large-set-quotient; large-quotient-Set; quotient-map-large-set-quotient;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient'; is-prop-type-class-large-set-quotient)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; map-equiv; inv-equiv; id-equiv; map-inv-equiv; inv-inv-equiv;
    right-inverse-law-equiv; left-inverse-law-equiv; distributive-inv-comp-equiv; is-equiv-has-inverse;
    right-unit-law-equiv; htpy-eq-equiv)
open import foundation.equivalence-relations using (Eq-Rel; refl-Eq-Rel)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functoriality-propositional-truncation using (functor-trunc-Prop)
open import foundation.empty-types using (ex-falso)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using (Id; inv; _∙_; ap; refl; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.mere-equivalences using (transitive-mere-equiv; mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop;
    all-elements-equal-type-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise; raise)
open import foundation.sets using (Id-Prop; UU-Set; type-Set; is-prop-is-set)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.unit-type using (star)
open import foundation.univalence using (equiv-eq; eq-equiv)
open import foundation.universe-levels using (Level; lzero; lsuc; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using
  ( hom-Concrete-Group; classifying-type-Concrete-Group;
    abstract-group-Concrete-Group; hom-group-hom-Concrete-Group;
    map-hom-Concrete-Group)
open import group-theory.groups using (set-Group)
open import group-theory.homomorphisms-generated-subgroups using
  ( restriction-generating-subset-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; htpy-hom-Group; comp-hom-Group; map-hom-Group)
open import group-theory.homomorphisms-semigroups using (preserves-mul)
open import group-theory.isomorphisms-groups using (hom-iso-Group; hom-inv-iso-Group)
open import group-theory.symmetric-groups using
  ( symmetric-Group; iso-symmetric-group-abstract-automorphism-group-Set)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; standard-2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-types using
  ( aut-point-Fin-two-ℕ; is-involution-aut-Fin-two-ℕ;
    preserves-add-aut-point-Fin-two-ℕ)
open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; equiv-count; has-decidable-equality-count)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin-Level)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set; has-decidable-equality-Fin; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; has-cardinality-type-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list; in-list)
open import univalent-combinatorics.orientations-complete-undirected-graph using
  ( quotient-sign; quotient-sign-Set; mere-equiv-Fin-2-quotient-sign;
    equiv-Fin-2-quotient-sign-equiv-Fin-n; map-orientation-Complete-Undirected-Graph-equiv;
    even-difference-orientation-Complete-Undirected-Graph;
    preserves-id-equiv-orientation-Complete-Undirected-Graph-equiv)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin; zero-Fin; nat-Fin; is-zero-nat-zero-Fin)
```

## Idea

## Definitions

```agda
module _
  { l : Level}
  where
  
  map-cartier-delooping-sign : (n : ℕ) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( UU-Set l)
        ( raise-Set l (Fin-Set n))
        ( is-one-type-UU-Set l)) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( UU-Set (lsuc l))
        ( raise-Set (lsuc l) (Fin-Set 2))
        ( is-one-type-UU-Set (lsuc l)))
  pr1 (map-cartier-delooping-sign zero-ℕ X) = raise-Set (lsuc l) (Fin-Set 2)
  pr2 (map-cartier-delooping-sign zero-ℕ X) = unit-trunc-Prop refl
  pr1 (map-cartier-delooping-sign (succ-ℕ zero-ℕ) X) = raise-Set (lsuc l) (Fin-Set 2)
  pr2 (map-cartier-delooping-sign (succ-ℕ zero-ℕ) X) = unit-trunc-Prop refl
  pr1 (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p)) =
    quotient-sign-Set
      ( succ-ℕ (succ-ℕ n))
      ( pair
        ( type-Set X)
        ( functor-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
  pr2 (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p)) =
    functor-trunc-Prop
      ( λ e →
        eq-pair-Σ
          ( eq-equiv
            ( type-Set (pr1 (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p))))
            ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
            ( equiv-raise (lsuc l) (Fin 2) ∘e inv-equiv e))
          ( eq-is-prop (is-prop-is-set (raise (lsuc l) (type-Set (Fin-Set 2))))))
      ( mere-equiv-Fin-2-quotient-sign
        ( succ-ℕ (succ-ℕ n))
        ( pair
          ( type-Set X)
          ( functor-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
        ( star))

  cartier-delooping-sign : (n : ℕ) →
    hom-Concrete-Group
      ( Automorphism-Group (UU-Set l) (raise-Set l (Fin-Set n)) (is-one-type-UU-Set l))
      ( Automorphism-Group (UU-Set (lsuc l)) (raise-Set (lsuc l) (Fin-Set 2)) (is-one-type-UU-Set (lsuc l)))
  pr1 (cartier-delooping-sign n) = map-cartier-delooping-sign n
  pr2 (cartier-delooping-sign zero-ℕ) = refl
  pr2 (cartier-delooping-sign (succ-ℕ zero-ℕ)) = refl
  pr2 (cartier-delooping-sign (succ-ℕ (succ-ℕ n))) =
    eq-pair-Σ
      ( eq-pair-Σ
        ( eq-equiv
          ( type-Set
            ( pr1
              ( map-cartier-delooping-sign
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( unit-trunc-Prop refl)))))
          ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
          ( equiv-raise (lsuc l) (Fin 2) ∘e
            inv-equiv
              ( equiv-Fin-2-quotient-sign-equiv-Fin-n
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                  ( functor-trunc-Prop
                    ( λ p' →
                      ( equiv-eq (inv (pr1 (pair-eq-Σ p')))) ∘e
                        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                    ( unit-trunc-Prop refl)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( eq-is-prop (is-prop-is-set _)))
      ( eq-is-prop is-prop-type-trunc-Prop)

  coherence-square-cartier-delooping-eq : (n : ℕ) →
    ( X Y : classifying-type-Concrete-Group
      ( Automorphism-Group (UU-Set l) (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))) (is-one-type-UU-Set l))) →
    ( p : Id X Y) →
    coherence-square
      ( map-orientation-Complete-Undirected-Graph-equiv (succ-ℕ (succ-ℕ n))
        ( pair
          ( pr1 (pr1 Y))
          ( functor-trunc-Prop
            ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( pr2 Y)))
        ( pair
          ( pr1 (pr1 X))
          ( functor-trunc-Prop
            ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( pr2 X)))
        ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ (inv p)))))))
      ( quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
          ( pair
            ( pr1 (pr1 X))
            ( functor-trunc-Prop
              ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( pr2 X)))))
      ( quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
          ( pair
            ( pr1 (pr1 Y))
            ( functor-trunc-Prop
              ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( pr2 Y)))))
      ( map-equiv
        ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ (ap (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n))) p)))))))
  coherence-square-cartier-delooping-eq n X .X refl x =
    ( ap
      ( quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( pr1 (pr1 X))
            ( functor-trunc-Prop
              ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
              (pr2 X)))))
      { x = x}
      { y =
        map-orientation-Complete-Undirected-Graph-equiv
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( pr1 (pr1 X))
            ( functor-trunc-Prop
              ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( pr2 X)))
          ( pair
            ( pr1 (pr1 X))
            ( functor-trunc-Prop
              ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( pr2 X)))
          ( id-equiv)
          ( x)}
      ( inv
        ( htpy-eq-equiv
          ( preserves-id-equiv-orientation-Complete-Undirected-Graph-equiv
            ( succ-ℕ (succ-ℕ n))
            (pair
              ( pr1 (pr1 X))
              ( functor-trunc-Prop
                ( λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( pr2 X))))
          ( x))))
{-
  eq-cartier-delooping-sign-trans : (n : ℕ) (ineq : leq-ℕ 2 n) →
    ( Y : 2-Element-Decidable-Subtype lzero (Fin n)) →
    Id
      ( map-hom-Concrete-Group
        ( Automorphism-Group
          ( UU-Set l)
          ( raise-Set l (Fin-Set n))
          ( is-one-type-UU-Set l))
        ( Automorphism-Group
          ( UU-Set (lsuc l))
          ( raise-Set (lsuc l) (Fin-Set 2))
          ( is-one-type-UU-Set (lsuc l)))
        ( cartier-delooping-sign n)
        ( eq-pair-Σ
          ( eq-pair-Σ
            ( eq-equiv
              ( type-Set (raise-Set l (Fin-Set n)))
              ( type-Set (raise-Set l (Fin-Set n)))
              ( equiv-raise l (Fin n) ∘e
                ( transposition Y ∘e inv-equiv (equiv-raise l (Fin n)))))
            ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l (Fin-Set n))))))
          ( eq-is-prop is-prop-type-trunc-Prop)))
      ( eq-pair-Σ
        ( eq-pair-Σ
          ( eq-equiv
            ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
            ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
            ( equiv-raise (lsuc l) (Fin 2) ∘e
              ( equiv-succ-Fin ∘e inv-equiv (equiv-raise (lsuc l) (Fin 2)))))
          ( eq-is-prop (is-prop-is-set (type-Set (raise-Set (lsuc l) (Fin-Set 2))))))
        ( eq-is-prop is-prop-type-trunc-Prop))
  eq-cartier-delooping-sign-trans (succ-ℕ (succ-ℕ n)) _ Y = {!!}
    where
    two-elements :
      Σ ( Fin (succ-ℕ (succ-ℕ n)))
        ( λ x →
          Σ ( Fin (succ-ℕ (succ-ℕ n)))
            ( λ y →
              Σ ( ¬ (Id x y))
                ( λ np →
                  Id
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-count (pair (succ-ℕ (succ-ℕ n)) id-equiv))
                      ( np))
                    ( Y))))
    two-elements =
      two-elements-transposition
        ( pair (succ-ℕ (succ-ℕ n)) id-equiv)
        ( Y)
    
  lemma : {l' : Level} (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (Fin-Set n))
        ( abstract-group-Concrete-Group
          ( Automorphism-Group
            ( UU-Set l)
            ( raise-Set l (Fin-Set n))
            ( is-one-type-UU-Set l)))
        ( abstract-group-Concrete-Group
          ( Automorphism-Group
            ( UU-Set (lsuc l))
            ( raise-Set (lsuc l) (Fin-Set 2))
            ( is-one-type-UU-Set (lsuc l))))
        ( hom-group-hom-Concrete-Group
          ( Automorphism-Group
            ( UU-Set l)
            ( raise-Set l (Fin-Set n))
            ( is-one-type-UU-Set l))
          ( Automorphism-Group
            ( UU-Set (lsuc l))
            ( raise-Set (lsuc l) (Fin-Set 2))
            ( is-one-type-UU-Set (lsuc l)))
          ( cartier-delooping-sign n))
        ( hom-iso-Group
          ( symmetric-Group (Fin-Set n))
          ( abstract-group-Concrete-Group
            ( Automorphism-Group
              ( UU-Set l)
              ( raise-Set l (Fin-Set n))
              ( is-one-type-UU-Set l)))
          ( iso-symmetric-group-abstract-automorphism-group-Set (Fin-Set n))))
      ( comp-hom-Group
        ( symmetric-Group (Fin-Set n))
        ( symmetric-Group (Fin-Set 2))
        ( abstract-group-Concrete-Group
          ( Automorphism-Group
            ( UU-Set (lsuc l))
            ( raise-Set (lsuc l) (Fin-Set 2))
            ( is-one-type-UU-Set (lsuc l))))
        ( hom-iso-Group
          ( symmetric-Group (Fin-Set 2))
          ( abstract-group-Concrete-Group
            ( Automorphism-Group
              ( UU-Set (lsuc l))
              ( raise-Set (lsuc l) (Fin-Set 2))
              ( is-one-type-UU-Set (lsuc l))))
          ( iso-symmetric-group-abstract-automorphism-group-Set (Fin-Set 2)))
        ( sign-homomorphism n (pair (Fin n) (unit-trunc-Prop id-equiv))))
  lemma {l'} n =
    map-inv-equiv
      ( equiv-ap-emb
        ( restriction-generating-subset-Group
          ( symmetric-Group (set-UU-Fin-Level (pair (Fin n) (unit-trunc-Prop id-equiv))))
          ( is-transposition-permutation-Prop {l2 = l'})
          ( is-generated-transposition-symmetric-Fin-Level n (pair (Fin n) (unit-trunc-Prop id-equiv)))
          ( abstract-group-Concrete-Group
            ( Automorphism-Group
              ( UU-Set (lsuc l))
              ( raise-Set (lsuc l) (Fin-Set 2))
              ( is-one-type-UU-Set (lsuc l))))))
      ( eq-htpy
        ( λ (pair Y p) →
          apply-universal-property-trunc-Prop
            ( p)
            ( Id-Prop
              ( set-Group
                ( abstract-group-Concrete-Group
                  ( Automorphism-Group
                    ( UU-Set (lsuc l))
                    ( raise-Set (lsuc l) (Fin-Set 2))
                    ( is-one-type-UU-Set (lsuc l)))))
              ?
              ?)
            ( λ (pair x p') →
              ( ( ap
                ( map-emb
                  ( restriction-generating-subset-Group
                    ( symmetric-Group (set-UU-Fin-Level (pair (Fin n) (unit-trunc-Prop id-equiv))))
                    ( is-transposition-permutation-Prop)
                    ( is-generated-transposition-symmetric-Fin-Level n
                      ( pair (Fin n) (unit-trunc-Prop id-equiv)))
                    ( abstract-group-Concrete-Group
                      ( Automorphism-Group
                        ( UU-Set (lsuc l))
                        ( raise-Set (lsuc l) (Fin-Set 2))
                        ( is-one-type-UU-Set (lsuc l)))))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set n))
                      ( abstract-group-Concrete-Group
                        ( Automorphism-Group
                          ( UU-Set l)
                          ( raise-Set l (Fin-Set n))
                          ( is-one-type-UU-Set l)))
                      ( abstract-group-Concrete-Group
                        ( Automorphism-Group
                          ( UU-Set (lsuc l))
                          ( raise-Set (lsuc l) (Fin-Set 2))
                          ( is-one-type-UU-Set (lsuc l))))
                      ( hom-group-hom-Concrete-Group
                        ( Automorphism-Group
                          ( UU-Set l)
                          ( raise-Set l (Fin-Set n))
                          ( is-one-type-UU-Set l))
                        ( Automorphism-Group
                          ( UU-Set (lsuc l))
                          ( raise-Set (lsuc l) (Fin-Set 2))
                          ( is-one-type-UU-Set (lsuc l)))
                        ( cartier-delooping-sign n))
                      ( hom-iso-Group
                        ( symmetric-Group (Fin-Set n))
                        ( abstract-group-Concrete-Group
                          ( Automorphism-Group
                            ( UU-Set l)
                            ( raise-Set l (Fin-Set n))
                            ( is-one-type-UU-Set l)))
                        ( iso-symmetric-group-abstract-automorphism-group-Set
                          ( Fin-Set n)))))
                { y = pair (transposition x) (unit-trunc-Prop (pair x refl))}
                ( eq-pair-Σ
                  ( inv p')
                  ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                ( {!ap!} ∙
                  {!!})))))-}
```
