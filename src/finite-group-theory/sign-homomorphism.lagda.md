---
title: The sign homomorphism
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.sign-homomorphism where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using (cong-zero-ℕ')
open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( add-Fin; mod-two-ℕ; mod-succ-add-ℕ; issec-nat-Fin; eq-mod-succ-cong-ℕ; ap-add-Fin)
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
open import foundation.contractible-types using (center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr; neq-inr-inl)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap-emb; map-emb)
open import foundation.equality-dependent-pair-types using (pair-eq-Σ; eq-pair-Σ)
open import foundation.equivalence-classes using
  ( equivalence-class; equivalence-class-Set; class;
    is-in-subtype-equivalence-class; is-decidable-is-in-subtype-equivalence-class-is-decidable;
    eq-effective-quotient'; is-prop-is-in-subtype-equivalence-class)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; map-equiv; inv-equiv; id-equiv; map-inv-equiv; inv-inv-equiv;
    right-inverse-law-equiv; left-inverse-law-equiv; distributive-inv-comp-equiv; is-equiv-has-inverse;
    right-unit-law-equiv; left-unit-law-equiv)
open import foundation.equivalence-relations using (Eq-Rel; refl-Eq-Rel)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functoriality-propositional-truncation using (map-trunc-Prop)
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
  ( has-decidable-equality-Fin; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; has-cardinality-type-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list; in-list)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin; zero-Fin; nat-Fin; is-zero-nat-zero-Fin; Fin-Set)
```

## Idea

The sign of a permutation is defined as the parity of the length of the decomposition of the permutation into transpositions. We show that each such decomposition as the same parity, so the sign map is well defined. We then show that the sign map is a group homomorphism.

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) 
  where

  sign-homomorphism-Fin-two : Aut (type-UU-Fin-Level n X) → Fin 2
  sign-homomorphism-Fin-two f =
    pr1 (center (is-contr-parity-transposition-permutation n X f))

  preserves-add-sign-homomorphism-Fin-two :
    (f g : (type-UU-Fin-Level n X) ≃ (type-UU-Fin-Level n X)) →
    Id ( sign-homomorphism-Fin-two (f ∘e g))
       ( add-Fin 2 (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g))
  preserves-add-sign-homomorphism-Fin-two f g =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin-Level n X)
      ( Id-Prop
        ( Fin-Set 2)
        ( sign-homomorphism-Fin-two (f ∘e g))
        ( add-Fin 2 (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g)))
      ( λ h →
        ( ap
          ( pr1)
          ( eq-is-contr
            ( is-contr-parity-transposition-permutation n X (f ∘e g))
            { x =
              center (is-contr-parity-transposition-permutation n X (f ∘e g))}
            { y =
              pair
                ( mod-two-ℕ (length-list (list-comp-f-g h)))
                ( unit-trunc-Prop
                  ( pair
                    ( list-comp-f-g h)
                    ( pair refl (eq-list-comp-f-g h))))})) ∙
        ( ( ap
            ( mod-two-ℕ)
            ( length-concat-list (list-trans f h) (list-trans g h))) ∙
          ( ( mod-succ-add-ℕ 1
              ( length-list (list-trans f h))
              ( length-list (list-trans g h))) ∙
            ( ( ap
                ( λ P →
                  add-Fin 2 (pr1 P) (mod-two-ℕ (length-list (list-trans g h))))
                { x =
                  pair
                    ( mod-two-ℕ (length-list (list-trans f h)))
                    ( unit-trunc-Prop
                      ( pair
                        ( list-trans f h)
                        ( pair
                          ( refl)
                          ( inv
                            ( eq-htpy-equiv
                              ( retr-permutation-list-transpositions-count
                                ( type-UU-Fin-Level n X)
                                ( pair n h)
                                ( f)))))))}
                { y = center (is-contr-parity-transposition-permutation n X f)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X f))) ∙
              ( ap
                ( λ P → add-Fin 2 (sign-homomorphism-Fin-two f) (pr1 P))
                { x =
                  pair
                    ( mod-two-ℕ (length-list (list-trans g h)))
                    ( unit-trunc-Prop
                      ( pair
                        ( list-trans g h)
                        ( pair
                          ( refl)
                          ( inv
                            ( eq-htpy-equiv
                              ( retr-permutation-list-transpositions-count
                                ( type-UU-Fin-Level n X)
                                ( pair n h)
                                ( g)))))))}
                { y = center (is-contr-parity-transposition-permutation n X g)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X g)))))))
    where
    list-trans :
      ( f' : (type-UU-Fin-Level n X) ≃ (type-UU-Fin-Level n X))
      ( h : Fin n ≃ type-UU-Fin-Level n X) →
      list
        ( Σ ( type-UU-Fin-Level n X → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level n X) (λ x → type-decidable-Prop (P x)))))
    list-trans f' h =
      list-transpositions-permutation-count (type-UU-Fin-Level n X) (pair n h) f'
    list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level n X) →
      list
        ( Σ ( (type-UU-Fin-Level n X) → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level n X) (λ x → type-decidable-Prop (P x)))))
    list-comp-f-g h = concat-list (list-trans f h) (list-trans g h)
    eq-list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level n X) →
      Id ( f ∘e g)
         ( permutation-list-transpositions
           ( list-comp-f-g h))
    eq-list-comp-f-g h =
      eq-htpy-equiv
        ( λ x →
          ( inv
            ( retr-permutation-list-transpositions-count
              ( type-UU-Fin-Level n X)
              ( pair n h)
              ( f)
              ( map-equiv g x))) ∙
          ( ap
            ( map-equiv
              ( permutation-list-transpositions
                ( list-trans f h)))
            ( inv
              ( retr-permutation-list-transpositions-count
                ( type-UU-Fin-Level n X)
                ( pair n h)
                ( g)
                ( x))))) ∙
              ( eq-concat-permutation-list-transpositions
                ( list-trans f h)
                ( list-trans g h))
```

### The sign homomorphism into the symmetric group S₂

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n)
  where

  map-sign-homomorphism : Aut (type-UU-Fin-Level n X) → Aut (Fin 2)
  map-sign-homomorphism f =
    aut-point-Fin-two-ℕ (sign-homomorphism-Fin-two n X f)

  preserves-comp-map-sign-homomorphism :
    preserves-mul _∘e_ _∘e_ map-sign-homomorphism
  preserves-comp-map-sign-homomorphism f g =
    ( ap
      ( aut-point-Fin-two-ℕ)
      ( preserves-add-sign-homomorphism-Fin-two n X f g)) ∙
    ( preserves-add-aut-point-Fin-two-ℕ
      ( sign-homomorphism-Fin-two n X f)
      ( sign-homomorphism-Fin-two n X g))
  
  sign-homomorphism :
    type-hom-Group
      ( symmetric-Group (set-UU-Fin-Level n X))
      ( symmetric-Group (Fin-Set 2))
  pr1 sign-homomorphism = map-sign-homomorphism
  pr2 sign-homomorphism = preserves-comp-map-sign-homomorphism

  eq-sign-homomorphism-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level n X)) →
    Id
      ( map-hom-Group
        ( symmetric-Group (set-UU-Fin-Level n X))
        ( symmetric-Group (Fin-Set 2))
        ( sign-homomorphism)
        ( transposition Y))
      ( equiv-succ-Fin 2)
  eq-sign-homomorphism-transposition Y =
    ap aut-point-Fin-two-ℕ
      ( ap pr1
        { x = center (is-contr-parity-transposition-permutation n X (transposition Y))}
        { y =
          pair
            ( inr star)
            ( unit-trunc-Prop
              ( pair
                ( in-list Y)
                ( pair refl (inv (right-unit-law-equiv (transposition Y))))))}
        ( eq-is-contr
          ( is-contr-parity-transposition-permutation n X (transposition Y))))
    
```
