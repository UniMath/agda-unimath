# The sign homomorphism

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.sign-homomorphism where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( add-Fin; mod-two-ℕ; mod-succ-add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import finite-group-theory.permutations using
  ( is-contr-parity-transposition-permutation;
    list-transpositions-permutation-count;
    retr-permutation-list-transpositions-count; is-generated-transposition-symmetric-Fin-Level)
open import finite-group-theory.transpositions using
  ( permutation-list-transpositions; eq-concat-permutation-list-transpositions;
    is-transposition-permutation-Prop; transposition; two-elements-transposition)

open import foundation.automorphisms using (Aut)
open import foundation.contractible-types using (center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap-emb; map-emb)
open import foundation.equality-dependent-pair-types using (pair-eq-Σ; eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; map-equiv; inv-equiv; id-equiv; map-inv-equiv;
    right-inverse-law-equiv; left-inverse-law-equiv)
open import foundation.equivalence-relations using (Eq-Rel)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functoriality-propositional-truncation using (functor-trunc-Prop)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using (Id; inv; _∙_; ap; refl; tr)
open import foundation.mere-equivalences using (transitive-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise; raise)
open import foundation.sets using (Id-Prop; UU-Set; type-Set; is-prop-is-set)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.unit-type using (star)
open import foundation.univalence using (equiv-eq; eq-equiv)
open import foundation.universe-levels using (Level; lzero; lsuc)

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
open import univalent-combinatorics.counting using (has-decidable-equality-count)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin-Level)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list)
open import univalent-combinatorics.orientations-complete-undirected-graph using
  ( quotient-sign; quotient-sign-Set; mere-equiv-Fin-2-quotient-sign; equiv-Fin-2-quotient-sign-equiv-Fin-n)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin; zero-Fin)
```

## Idea

The sign of a permutation is defined as the parity of the length of the decomposition of the permutation into transpositions. We show that each such decomposition as the same parity, so the sign map is well defined. We then show that the sign map is a group homomorphism.

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) 
  where

  sign-homomorphism-Fin-two : Aut (type-UU-Fin-Level X) → Fin 2
  sign-homomorphism-Fin-two f =
    pr1 (center (is-contr-parity-transposition-permutation n X f))

  preserves-add-sign-homomorphism-Fin-two :
    (f g : (type-UU-Fin-Level X) ≃ (type-UU-Fin-Level X)) →
    Id ( sign-homomorphism-Fin-two (f ∘e g))
       ( add-Fin (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g))
  preserves-add-sign-homomorphism-Fin-two f g =
    apply-universal-property-trunc-Prop
      ( mere-equiv-UU-Fin-Level X)
      ( Id-Prop
        ( Fin-Set 2)
        ( sign-homomorphism-Fin-two (f ∘e g))
        ( add-Fin (sign-homomorphism-Fin-two f) (sign-homomorphism-Fin-two g)))
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
                  add-Fin (pr1 P) (mod-two-ℕ (length-list (list-trans g h))))
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
                                ( type-UU-Fin-Level X)
                                ( pair n h)
                                ( f)))))))}
                { y = center (is-contr-parity-transposition-permutation n X f)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X f))) ∙
              ( ap
                ( λ P → add-Fin (sign-homomorphism-Fin-two f) (pr1 P))
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
                                ( type-UU-Fin-Level X)
                                ( pair n h)
                                ( g)))))))}
                { y = center (is-contr-parity-transposition-permutation n X g)}
                ( eq-is-contr
                  ( is-contr-parity-transposition-permutation n X g)))))))
    where
    list-trans :
      ( f' : (type-UU-Fin-Level X) ≃ (type-UU-Fin-Level X))
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      list
        ( Σ ( type-UU-Fin-Level X → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))))
    list-trans f' h =
      list-transpositions-permutation-count (type-UU-Fin-Level X) (pair n h) f'
    list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      list
        ( Σ ( (type-UU-Fin-Level X) → decidable-Prop l)
            ( λ P →
              has-cardinality 2
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))))
    list-comp-f-g h = concat-list (list-trans f h) (list-trans g h)
    eq-list-comp-f-g :
      ( h : Fin n ≃ type-UU-Fin-Level X) →
      Id ( f ∘e g)
         ( permutation-list-transpositions
           ( list-comp-f-g h))
    eq-list-comp-f-g h =
      eq-htpy-equiv
        ( λ x →
          ( inv
            ( retr-permutation-list-transpositions-count
              ( type-UU-Fin-Level X)
              ( pair n h)
              ( f)
              ( map-equiv g x))) ∙
          ( ap
            ( map-equiv
              ( permutation-list-transpositions
                ( list-trans f h)))
            ( inv
              ( retr-permutation-list-transpositions-count
                ( type-UU-Fin-Level X)
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

  map-sign-homomorphism : Aut (type-UU-Fin-Level X) → Aut (Fin 2)
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
      ( symmetric-Group (set-UU-Fin-Level X))
      ( symmetric-Group (Fin-Set 2))
  pr1 sign-homomorphism = map-sign-homomorphism
  pr2 sign-homomorphism = preserves-comp-map-sign-homomorphism
```

### Deloopings of the sign homomorphism

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

### Simpson's delooping of the sign homomorphism

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n)
  where

  sign-comp-Rel : Eq-Rel lzero (Fin n ≃ type-UU-Fin-Level X)
  pr1 sign-comp-Rel f g =
    Id-Prop (Fin-Set 2) zero-Fin (sign-homomorphism-Fin-two n X (f ∘e inv-equiv g))
  pr1 (pr2 sign-comp-Rel) {f} =
    ap pr1
      { x = pair zero-Fin (unit-trunc-Prop (pair nil (pair refl (right-inverse-law-equiv f))))}
      { y = center (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f))}
      ( eq-is-contr (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f)))
  pr1 (pr2 (pr2 sign-comp-Rel)) {f} {g} P =
    ap pr1
      { x = pair zero-Fin (unit-trunc-Prop (pair nil (pair refl (left-inverse-law-equiv (f ∘e inv-equiv g)))))}
      { y = center (is-contr-parity-transposition-permutation n X (inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n X
          ( inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))) ∙
      ( ( preserves-add-sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)) (f ∘e inv-equiv g)) ∙
        ( ( ap
          ( add-Fin (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g))))
          ( inv P)) ∙
          ( {!!} ∙ {!!})))
  pr2 (pr2 (pr2 sign-comp-Rel)) = {!!}

