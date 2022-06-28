# The sign homomorphism

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
  ( large-set-quotient; large-quotient-Set; quotient-map-large-set-quotient;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient'; is-prop-type-class-large-set-quotient)
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
  ( Fin-Set; has-decidable-equality-Fin; two-distinct-elements-leq-2-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; has-cardinality-type-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list; in-list)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin; zero-Fin; nat-Fin; is-zero-nat-zero-Fin)
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
      ( has-cardinality-type-UU-Fin-Level X)
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

  eq-sign-homomorphism-transposition :
    ( Y : 2-Element-Decidable-Subtype l (type-UU-Fin-Level X)) →
    Id
      ( map-hom-Group
        ( symmetric-Group (set-UU-Fin-Level X))
        ( symmetric-Group (Fin-Set 2))
        ( sign-homomorphism)
        ( transposition Y))
      equiv-succ-Fin
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

## Deloopings of the sign homomorphism

### Simpson's delooping of the sign homomorphism

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n)
  where

  sign-comp-Eq-Rel : Eq-Rel lzero (Fin n ≃ type-UU-Fin-Level X)
  pr1 sign-comp-Eq-Rel f g =
    Id-Prop (Fin-Set 2) zero-Fin (sign-homomorphism-Fin-two n X (f ∘e inv-equiv g))
  pr1 (pr2 sign-comp-Eq-Rel) {f} =
    ap pr1
      { x = pair zero-Fin (unit-trunc-Prop (pair nil (pair refl (right-inverse-law-equiv f))))}
      { y = center (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f))}
      ( eq-is-contr (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f)))
  pr1 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} P =
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
          ( ( ap
            ( λ k →
              mod-two-ℕ (add-ℕ (nat-Fin (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) k))
            ( is-zero-nat-zero-Fin {k = 1})) ∙
            ( ( issec-nat-Fin (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) ∙
              ( ap
                ( sign-homomorphism-Fin-two n X)
                ( ( distributive-inv-comp-equiv (inv-equiv g) f) ∙
                  ap (λ h → h ∘e inv-equiv f) (inv-inv-equiv g)))))))
  pr2 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} {h} P Q =
    ( ap mod-two-ℕ
      ( ( ap (add-ℕ zero-ℕ) (inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap nat-Fin Q)) ∙
        ( ap
          ( λ k → add-ℕ k (nat-Fin (sign-homomorphism-Fin-two n X (g ∘e inv-equiv h))))
          ( inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap nat-Fin P)))) ∙
      ( ( inv
        ( preserves-add-sign-homomorphism-Fin-two n X (f ∘e inv-equiv g) (g ∘e inv-equiv h))) ∙
        ( ap
          ( sign-homomorphism-Fin-two n X)
          ( ( eq-htpy-equiv refl-htpy) ∙
            ( ap (λ h' → f ∘e (h' ∘e inv-equiv h)) (left-inverse-law-equiv g) ∙
              ( eq-htpy-equiv refl-htpy)))))

  quotient-sign-comp : UU (lsuc lzero ⊔ l)
  quotient-sign-comp = large-set-quotient sign-comp-Eq-Rel

  quotient-sign-comp-Set : UU-Set (lsuc lzero ⊔ l)
  quotient-sign-comp-Set = large-quotient-Set sign-comp-Eq-Rel

module _
  {l : Level} {X : UU l} (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  private abstract
    lemma :
      Id
        ( inr star)
        ( pr1
          ( center
            ( is-contr-parity-transposition-permutation
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( equiv-count eX ∘e
                inv-equiv
                  (equiv-count eX ∘e
                    transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-Fin)
                          ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))))
    lemma =
      ap pr1
        { x =
          pair
            ( inr star)
            ( unit-trunc-Prop
              ( pair
                ( in-list
                  ( transposition-conjugation-equiv
                    ( Fin (number-of-elements-count eX))
                    ( X)
                    ( equiv-count eX)
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-Fin)
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                ( pair
                  ( refl)
                  ( ( ap
                    ( λ e → equiv-count eX ∘e e)
                    ( distributive-inv-comp-equiv
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-Fin)
                          ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                      ( equiv-count eX))) ∙
                      ( ( ap
                        ( λ e → equiv-count eX ∘e (e ∘e inv-equiv (equiv-count eX)))
                        ( ( own-inverse-is-involution
                          ( is-involution-map-transposition
                            ( standard-2-Element-Decidable-Subtype
                              ( has-decidable-equality-Fin)
                              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))) ∙
                          ( inv
                            ( right-unit-law-equiv
                              ( transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin)
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))) ∙
                          ( inv
                            ( eq-htpy-equiv
                              ( correct-transposition-conjugation-equiv-list
                                ( Fin (number-of-elements-count eX))
                                ( X)
                                ( equiv-count eX)
                                ( in-list
                                  ( standard-2-Element-Decidable-Subtype
                                    ( has-decidable-equality-Fin)
                                    ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))))))))}
        { y =
          center
            ( is-contr-parity-transposition-permutation
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX)))
              ( equiv-count eX ∘e
                inv-equiv
                  ( equiv-count eX ∘e
                    transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-Fin)
                        ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))}
        ( eq-is-contr
          ( is-contr-parity-transposition-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( equiv-count eX ∘e
              inv-equiv
                ( equiv-count eX ∘e
                  transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-Fin)
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))

  inv-Fin-2-quotient-sign-comp-count :
    ( T : quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( type-class-large-set-quotient
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
    Fin 2
  inv-Fin-2-quotient-sign-comp-count T (inl P) = inl (inr star)
  inv-Fin-2-quotient-sign-comp-count T (inr NP) = inr star

  equiv-Fin-2-quotient-sign-comp-count : Fin 2 ≃
    quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
  pr1 equiv-Fin-2-quotient-sign-comp-count (inl (inr star)) =
    quotient-map-large-set-quotient
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX)
  pr1 equiv-Fin-2-quotient-sign-comp-count (inr star) =
    quotient-map-large-set-quotient
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX ∘e
        transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-Fin)
            ( pr2 (pr2 ( two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
  pr2 equiv-Fin-2-quotient-sign-comp-count =
    is-equiv-has-inverse
      (λ T →
        inv-Fin-2-quotient-sign-comp-count T
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin
                ( zero-Fin)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ T →
        retr-Fin-2-quotient-sign-comp-count T
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin zero-Fin
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ k →
        sec-Fin-2-quotient-sign-comp-count k
          ( is-decidable-type-class-large-set-quotient-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin zero-Fin
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
            ( equiv-count eX)))
    where
    cases-retr-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ¬ ( type-class-large-set-quotient
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
      ( f : Fin (number-of-elements-count eX) ≃ X) →
      Id
        ( quotient-map-large-set-quotient
          ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
          ( f))
        ( T) →
      ( k : Fin 2) →
      Id
        ( k)
        ( sign-homomorphism-Fin-two
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( f ∘e inv-equiv (equiv-count eX))) →
      type-class-large-set-quotient
        ( sign-comp-Eq-Rel
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX ∘e
          transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-Fin)
              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))    
    cases-retr-Fin-2-quotient-sign-comp-count T NP f p (inl (inr star)) q =
      ex-falso
        ( NP
          ( tr
            ( λ x →
              type-class-large-set-quotient
                ( sign-comp-Eq-Rel
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( x)
                ( equiv-count eX))
            ( p)
            ( q)))
    cases-retr-Fin-2-quotient-sign-comp-count T NP f p (inr star) q =
      tr
        ( λ x →
          type-class-large-set-quotient
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( x)
            ( equiv-count eX ∘e
              transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-Fin)
                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
        ( p)
        ( ( eq-mod-succ-cong-ℕ 1 0 2 (cong-zero-ℕ' 2)) ∙
          ( ( ap-add-Fin
            ( q)
            ( lemma)) ∙
            ( ( inv
              ( preserves-add-sign-homomorphism-Fin-two
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( f ∘e inv-equiv (equiv-count eX))
                ( equiv-count eX ∘e
                  inv-equiv
                    ( equiv-count eX ∘e
                      transposition
                        ( standard-2-Element-Decidable-Subtype has-decidable-equality-Fin
                        ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
              ( ap
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( ( eq-htpy-equiv refl-htpy) ∙
                  ( ap
                    ( λ h →
                      f ∘e
                        ( h ∘e
                          inv-equiv
                            ( equiv-count eX ∘e
                              transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin)
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))
                    (left-inverse-law-equiv (equiv-count eX)) ∙
                    ( eq-htpy-equiv refl-htpy)))))))
    retr-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ( H : is-decidable
        (type-class-large-set-quotient
          ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
          ( T)
          ( equiv-count eX))) →
      Id
        ( pr1 equiv-Fin-2-quotient-sign-comp-count (inv-Fin-2-quotient-sign-comp-count T H))
        ( T)
    retr-Fin-2-quotient-sign-comp-count T (inl P) =
      eq-effective-quotient'
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( equiv-count eX)
        ( T)
        ( P)
    retr-Fin-2-quotient-sign-comp-count T (inr NP) =
      eq-effective-quotient'
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( equiv-count eX ∘e
          transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-Fin)
              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( pair
            ( type-class-large-set-quotient
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin)
                    ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
            ( is-prop-type-class-large-set-quotient
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  (standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin)
                    ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))
          ( λ (pair t p) →
            cases-retr-Fin-2-quotient-sign-comp-count
              ( T)
              ( NP)
              ( t)
              ( eq-pair-Σ
                ( p)
                ( all-elements-equal-type-trunc-Prop _ (pr2 T)))
              ( sign-homomorphism-Fin-two (number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( t ∘e inv-equiv (equiv-count eX)))
              ( refl)))
    sec-Fin-2-quotient-sign-comp-count : (k : Fin 2) →
      ( D : is-decidable
        ( type-class-large-set-quotient
          ( sign-comp-Eq-Rel
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
          ( equiv-count eX))) →
      Id
        ( inv-Fin-2-quotient-sign-comp-count
          ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
          ( D))
        ( k)
    sec-Fin-2-quotient-sign-comp-count (inl (inr star)) (inl D) = refl
    sec-Fin-2-quotient-sign-comp-count (inl (inr star)) (inr ND) =
      ex-falso
        ( ND
          ( refl-Eq-Rel
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))))
    sec-Fin-2-quotient-sign-comp-count (inr star) (inl D) =
      ex-falso
        ( neq-inr-inl
          (lemma ∙
            ( inv
              ( D ∙
                ( ap
                  ( sign-homomorphism-Fin-two
                    ( number-of-elements-count eX)
                    ( pair X (unit-trunc-Prop (equiv-count eX))))
                  ( eq-htpy-equiv refl-htpy ∙
                    ( ( ap
                      ( λ h → equiv-count eX ∘e h)
                      ( ( ap
                        ( λ h → h ∘e inv-equiv (equiv-count eX))
                        { x =
                          transposition
                            (standard-2-Element-Decidable-Subtype
                              has-decidable-equality-Fin
                              (pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))}
                        ( inv
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin)
                                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
                        ( inv
                          ( distributive-inv-comp-equiv
                            ( transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin)
                                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                            ( equiv-count eX))))) ∙
                      ( eq-htpy-equiv refl-htpy))))))))
    sec-Fin-2-quotient-sign-comp-count (inr star) (inr ND) = refl

module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (ineq : leq-ℕ 2 n)
  where
  
  equiv-Fin-2-quotient-sign-comp-equiv-Fin-n : (h : Fin n ≃ type-UU-Fin-Level X) →
    ( Fin 2 ≃ quotient-sign-comp n X)
  equiv-Fin-2-quotient-sign-comp-equiv-Fin-n h =
    tr
      ( λ e → Fin 2 ≃ quotient-sign-comp n (pair (type-UU-Fin-Level X) e))
      ( all-elements-equal-type-trunc-Prop (unit-trunc-Prop (equiv-count (pair n h))) (pr2 X))
      ( equiv-Fin-2-quotient-sign-comp-count (pair n h) ineq)
    
  abstract
    mere-equiv-Fin-2-quotient-sign-comp :
      mere-equiv (Fin 2) (quotient-sign-comp n X)
    mere-equiv-Fin-2-quotient-sign-comp =
      map-trunc-Prop
        ( equiv-Fin-2-quotient-sign-comp-equiv-Fin-n)
        ( has-cardinality-type-UU-Fin-Level X)

module _
  { l : Level}
  where
  
  map-simpson-delooping-sign : (n : ℕ) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( UU-Set l)
        ( raise-Set l (Fin-Set n))
        ( is-one-type-UU-Set l)) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( UU-Set (lsuc lzero ⊔ l))
        ( raise-Set (lsuc lzero ⊔ l) (Fin-Set 2))
        ( is-one-type-UU-Set (lsuc lzero ⊔ l)))
  pr1 (map-simpson-delooping-sign zero-ℕ X) = raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)
  pr2 (map-simpson-delooping-sign zero-ℕ X) = unit-trunc-Prop refl
  pr1 (map-simpson-delooping-sign (succ-ℕ zero-ℕ) X) = raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)
  pr2 (map-simpson-delooping-sign (succ-ℕ zero-ℕ) X) = unit-trunc-Prop refl
  pr1 (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p)) =
    quotient-sign-comp-Set
      ( succ-ℕ (succ-ℕ n))
      ( pair
        ( type-Set X)
        ( map-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
  pr2 (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p)) =
    map-trunc-Prop
      ( λ e →
        eq-pair-Σ
          ( eq-equiv
            ( type-Set (pr1 (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p))))
            ( type-Set (raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)))
            ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e inv-equiv e))
          ( eq-is-prop (is-prop-is-set (raise (lsuc lzero ⊔ l) (type-Set (Fin-Set 2))))))
      ( mere-equiv-Fin-2-quotient-sign-comp
        ( succ-ℕ (succ-ℕ n))
        ( pair
          ( type-Set X)
          ( map-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
        ( star))

  simpson-delooping-sign : (n : ℕ) →
    hom-Concrete-Group
      ( Automorphism-Group (UU-Set l) (raise-Set l (Fin-Set n)) (is-one-type-UU-Set l))
      ( Automorphism-Group
        ( UU-Set (lsuc lzero ⊔ l))
        ( raise-Set (lsuc lzero ⊔ l) (Fin-Set 2))
        ( is-one-type-UU-Set (lsuc lzero ⊔ l)))
  pr1 (simpson-delooping-sign n) = map-simpson-delooping-sign n
  pr2 (simpson-delooping-sign zero-ℕ) = refl
  pr2 (simpson-delooping-sign (succ-ℕ zero-ℕ)) = refl
  pr2 (simpson-delooping-sign (succ-ℕ (succ-ℕ n))) =
    eq-pair-Σ
      ( eq-pair-Σ
        ( eq-equiv
          ( type-Set
            ( pr1
              ( map-simpson-delooping-sign
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( unit-trunc-Prop refl)))))
          ( type-Set (raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)))
          ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e
            inv-equiv
              ( equiv-Fin-2-quotient-sign-comp-equiv-Fin-n
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                  ( map-trunc-Prop
                    ( λ p' →
                      ( equiv-eq (inv (pr1 (pair-eq-Σ p')))) ∘e
                        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                    ( unit-trunc-Prop refl)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( eq-is-prop (is-prop-is-set _)))
      ( eq-is-prop is-prop-type-trunc-Prop)
```
