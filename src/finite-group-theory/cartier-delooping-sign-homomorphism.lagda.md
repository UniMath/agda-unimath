# Cartier's delooping of the sign homomorphism

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
open import foundation.contractible-types using (is-contr; center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr; neq-inr-inl)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap-emb; map-emb)
open import foundation.equality-dependent-pair-types using
  ( pair-eq-Σ; eq-pair-Σ; comp-eq-pair-Σ)
open import foundation.equivalence-classes using
  ( large-set-quotient; large-quotient-Set; quotient-map-large-set-quotient;
    type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable;
    eq-effective-quotient'; is-prop-type-class-large-set-quotient;
    quotient-reflecting-map-large-set-quotient)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; map-equiv; inv-equiv; id-equiv; map-inv-equiv; inv-inv-equiv;
    right-inverse-law-equiv; left-inverse-law-equiv; distributive-inv-comp-equiv; is-equiv-has-inverse;
    right-unit-law-equiv; htpy-eq-equiv)
open import foundation.equivalence-relations using (Eq-Rel; refl-Eq-Rel)
open import foundation.functions using (_∘_)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functoriality-propositional-truncation using (functor-trunc-Prop)
open import foundation.functoriality-set-quotients using
  ( unique-equiv-is-set-quotient; equiv-is-set-quotient)
open import foundation.empty-types using (ex-falso)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using
  ( Id; inv; _∙_; ap; refl; tr; ap-concat; distributive-inv-concat)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.mere-equivalences using
  ( transitive-mere-equiv; symmetric-mere-equiv; mere-equiv; is-set-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop;
    all-elements-equal-type-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise; raise)
open import foundation.sets using
  ( is-set; Id-Prop; UU-Set; type-Set; is-set-type-Set; is-prop-is-set; is-set-equiv)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.unit-type using (star)
open import foundation.univalence using (equiv-eq; eq-equiv)
open import foundation.universal-property-set-quotients using (is-set-quotient-large-set-quotient)
open import foundation.universe-levels using (Level; lzero; lsuc; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using
  ( hom-Concrete-Group; classifying-type-Concrete-Group;
    abstract-group-Concrete-Group; hom-group-hom-Concrete-Group;
    map-hom-Concrete-Group)
open import group-theory.groups using
  ( set-Group; type-Group; mul-Group)
open import group-theory.homomorphisms-generated-subgroups using
  ( restriction-generating-subset-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; htpy-hom-Group; comp-hom-Group; map-hom-Group; preserves-mul-hom-Group)
open import group-theory.homomorphisms-semigroups using (preserves-mul)
open import group-theory.isomorphisms-groups using (hom-iso-Group; hom-inv-iso-Group)
open import group-theory.loop-groups-sets using
  ( loop-group-Set; map-hom-symmetric-group-loop-group-Set; hom-symmetric-group-loop-group-Set)
open import group-theory.symmetric-groups using
  ( symmetric-Group; iso-symmetric-group-abstract-automorphism-group-Set;
    iso-symmetric-group-equiv-Set)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; standard-2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-types using
  ( aut-point-Fin-two-ℕ; is-involution-aut-Fin-two-ℕ;
    preserves-add-aut-point-Fin-two-ℕ)
open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; equiv-count; has-decidable-equality-count; is-set-count)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin-Level)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Fin-Set; has-decidable-equality-Fin; two-distinct-elements-leq-2-Fin; is-set-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality; has-cardinality-type-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( list; cons; nil; concat-list; length-list; length-concat-list; reverse-list; in-list)
open import univalent-combinatorics.orientations-complete-undirected-graph using
  ( quotient-sign; quotient-sign-Set; mere-equiv-Fin-2-quotient-sign;
    equiv-Fin-2-quotient-sign-equiv-Fin-n; map-orientation-complete-undirected-graph-equiv;
    even-difference-orientation-Complete-Undirected-Graph;
    preserves-even-difference-orientation-complete-undirected-graph-equiv;
    preserves-id-equiv-orientation-complete-undirected-graph-equiv;
    equiv-Fin-2-quotient-sign-count; orientation-complete-undirected-graph-equiv)
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

  abstract
    eq-Fin-2-map-cartier-delooping-sign-count : (n : ℕ) →
      ( X : UU lzero) (eX : Fin n ≃ X) →
      Id
        ( map-cartier-delooping-sign n
          ( pair
            ( raise-Set l (pair X (is-set-count (pair n eX))))
            ( unit-trunc-Prop
              ( eq-pair-Σ
                ( eq-equiv
                  ( raise l X)
                  ( raise l (Fin n))
                  ( equiv-raise l (Fin n) ∘e (inv-equiv eX ∘e inv-equiv (equiv-raise l X))))
                ( eq-is-prop (is-prop-is-set (raise l (Fin n))))))))
        ( pair (raise-Set (lsuc l) (Fin-Set 2)) (unit-trunc-Prop refl))
    eq-Fin-2-map-cartier-delooping-sign-count zero-ℕ X eX = refl
    eq-Fin-2-map-cartier-delooping-sign-count (succ-ℕ zero-ℕ) X eX = refl
    eq-Fin-2-map-cartier-delooping-sign-count (succ-ℕ (succ-ℕ n)) X eX =
      eq-pair-Σ
        ( eq-pair-Σ
          ( eq-equiv
            ( type-Set
              ( pr1
                ( map-cartier-delooping-sign
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise-Set l (pair X (is-set-count (pair (succ-ℕ (succ-ℕ n)) eX))))
                    ( unit-trunc-Prop
                      ( eq-pair-Σ
                        ( eq-equiv
                          ( raise l X)
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))) ∘e
                            ( inv-equiv eX ∘e inv-equiv (equiv-raise l X))))
                        ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))))))))
            ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
            ( equiv-raise (lsuc l) (Fin 2) ∘e
              inv-equiv
                ( equiv-Fin-2-quotient-sign-equiv-Fin-n
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (type-Set (pair X (is-set-count (pair (succ-ℕ (succ-ℕ n)) eX)))))
                    ( functor-trunc-Prop
                      ( λ p' →
                        equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e
                          equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop
                        ( eq-pair-Σ
                          ( eq-equiv (raise l X) (raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))) ∘e
                            ( inv-equiv eX ∘e inv-equiv (equiv-raise l X))))
                        ( eq-is-prop
                          ( is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))))))
                  ( star)
                  ( equiv-raise l X ∘e eX))))
          ( eq-is-prop (is-prop-is-set _)))
        ( eq-is-prop is-prop-type-trunc-Prop)

  cartier-delooping-sign : (n : ℕ) →
    hom-Concrete-Group
      ( Automorphism-Group (UU-Set l) (raise-Set l (Fin-Set n)) (is-one-type-UU-Set l))
      ( Automorphism-Group (UU-Set (lsuc l)) (raise-Set (lsuc l) (Fin-Set 2)) (is-one-type-UU-Set (lsuc l)))
  pr1 (cartier-delooping-sign n) = map-cartier-delooping-sign n
  pr2 (cartier-delooping-sign n) =
    tr
      ( λ w →
        Id
          ( map-cartier-delooping-sign n
            ( pair
              ( pair
                ( raise l (Fin n))
                ( pr1 w))
              ( pr2 w)))
          ( pair (raise-Set (lsuc l) (Fin-Set 2)) (unit-trunc-Prop refl)))
      ( eq-pair-Σ
        ( eq-is-prop ( is-prop-is-set (raise l (Fin n))))
        ( eq-is-prop is-prop-type-trunc-Prop))
      ( eq-Fin-2-map-cartier-delooping-sign-count n (Fin n) id-equiv)

module _
  { l : Level}
  where

  map-cartier-delooping-sign-loop : (n : ℕ) (X Y : UU l) →
    (eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) (eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
    Id X Y →
    Id
      ( quotient-sign (succ-ℕ (succ-ℕ n)) (pair X eX))
      ( quotient-sign (succ-ℕ (succ-ℕ n)) (pair Y eY))
  map-cartier-delooping-sign-loop n X Y eX eY p =
    ap (quotient-sign (succ-ℕ (succ-ℕ n))) (eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))
    
  cartier-delooping-sign-loop : (n : ℕ) →
    type-hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
      ( loop-group-Set
        ( quotient-sign-Set
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
  pr1 (cartier-delooping-sign-loop n) =
    map-cartier-delooping-sign-loop n
      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
  pr2 (cartier-delooping-sign-loop n) p q =
    ( ap
      ( ap (quotient-sign (succ-ℕ (succ-ℕ n))))
      ( ( ap
        ( λ w → eq-pair-Σ (p ∙ q) w)
        ( eq-is-prop
          ( is-trunc-Id
            ( is-prop-type-trunc-Prop _ (unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))) ∙
        ( inv
          ( comp-eq-pair-Σ
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( p)
            ( q)
            ( eq-is-prop is-prop-type-trunc-Prop)
            ( eq-is-prop is-prop-type-trunc-Prop))))) ∙
      ( ap-concat
        ( quotient-sign (succ-ℕ (succ-ℕ n)))
        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))
        ( eq-pair-Σ q (eq-is-prop is-prop-type-trunc-Prop)))

  abstract
    coherence-square-map-cartier-delooping-sign-loop-Set : (n : ℕ) (X Y : UU l) (eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) →
      ( eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
      ( p : Id X Y) → (Id (tr (λ v → mere-equiv (Fin (succ-ℕ (succ-ℕ n))) v) p eX) eY) →
      ( sX : is-set X) ( sY : is-set Y) →
      coherence-square
        ( map-orientation-complete-undirected-graph-equiv
          ( succ-ℕ (succ-ℕ n))
          ( pair X eX)
          ( pair Y eY)
          ( map-hom-symmetric-group-loop-group-Set
            ( pair Y sY)
            ( pair X sX)
            ( inv p)))
        ( quotient-map-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair Y eY)))
        ( quotient-map-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair X eX)))
        ( map-equiv
          ( map-hom-symmetric-group-loop-group-Set
            ( quotient-sign-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
            ( quotient-sign-Set (succ-ℕ (succ-ℕ n)) (pair Y eY))
            ( map-cartier-delooping-sign-loop n X Y eX eY p)))
    coherence-square-map-cartier-delooping-sign-loop-Set n X .X eX .eX refl refl sX sY x =
      ( ap
        ( λ w →
          map-equiv
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-sign-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( quotient-sign-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( w))
            ( quotient-map-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph
                ( succ-ℕ (succ-ℕ n))
                ( pair X eX))
              ( x)))
        ( ap
          ( λ w → ap (quotient-sign (succ-ℕ (succ-ℕ n))) (eq-pair-Σ refl w))
          { x = eq-is-prop is-prop-type-trunc-Prop}
          ( eq-is-prop
            ( is-trunc-Id
              ( is-prop-type-trunc-Prop
                ( tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX)
                ( eX)))))) ∙
        ( ap
          ( quotient-map-large-set-quotient
            ( even-difference-orientation-Complete-Undirected-Graph
              ( succ-ℕ (succ-ℕ n))
              ( pair X (tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX))))
          ( inv
            ( htpy-eq-equiv
              ( preserves-id-equiv-orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( x))))

  coherence-square-map-cartier-delooping-sign-loop-Fin : (n : ℕ) 
    ( p : Id (raise l (Fin (succ-ℕ (succ-ℕ n)))) (raise l (Fin (succ-ℕ (succ-ℕ n))))) →
    coherence-square
      ( map-orientation-complete-undirected-graph-equiv
        ( succ-ℕ (succ-ℕ n))
        ( pair
          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
          ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
        ( pair
          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
          ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( inv p)))
      ( quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
      ( quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( pair
            (raise l (Fin (succ-ℕ (succ-ℕ n))))
            (unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-Set
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( quotient-sign-Set
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( map-cartier-delooping-sign-loop n
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( p))))
  coherence-square-map-cartier-delooping-sign-loop-Fin n p =
    coherence-square-map-cartier-delooping-sign-loop-Set n
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( p)
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( is-set-type-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
      ( is-set-type-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))

  private abstract
    is-contr-equiv-orientation : (n : ℕ) →
      ( p : Id (raise l (Fin (succ-ℕ (succ-ℕ n)))) (raise l (Fin (succ-ℕ (succ-ℕ n))))) →
      is-contr
        ( Σ
          ( quotient-sign
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))) ≃
            quotient-sign
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( λ h' →
            coherence-square
              ( map-equiv
                ( orientation-complete-undirected-graph-equiv
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                    ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                  ( pair
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                    ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( inv p))))
              ( quotient-map-large-set-quotient
                ( even-difference-orientation-Complete-Undirected-Graph
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                    ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
              ( quotient-map-large-set-quotient
                ( even-difference-orientation-Complete-Undirected-Graph
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                    ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
              ( map-equiv h')))
    is-contr-equiv-orientation n p =
      unique-equiv-is-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( quotient-sign-Set
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( quotient-reflecting-map-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) (unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( quotient-sign-Set
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
        ( quotient-reflecting-map-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
        ( is-set-quotient-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
        ( is-set-quotient-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
        ( orientation-complete-undirected-graph-equiv
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
            ( raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n))))
            ( inv p)))
        ( λ {x} {y} →
          preserves-even-difference-orientation-complete-undirected-graph-equiv
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( equiv-eq (inv (inv p)))
            ( x)
            ( y))

  abstract
    eq-cartier-delooping-sign-loop-equiv-is-set-quotient : (n : ℕ) →
      ( p : Id (raise l (Fin (succ-ℕ (succ-ℕ n)))) (raise l (Fin (succ-ℕ (succ-ℕ n))))) →
      Id 
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-Set
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( quotient-sign-Set
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( map-cartier-delooping-sign-loop n
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( p)))
        (pr1 (center (is-contr-equiv-orientation n p)))
    eq-cartier-delooping-sign-loop-equiv-is-set-quotient n p =
      ap pr1
        { x =
          pair
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-sign-Set
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                  ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
              ( quotient-sign-Set
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                  ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
              ( map-cartier-delooping-sign-loop n
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( p)))
            ( coherence-square-map-cartier-delooping-sign-loop-Fin n p)}
        { y = center (is-contr-equiv-orientation n p)}
        ( eq-is-contr (is-contr-equiv-orientation n p))

  hom-equiv-is-set-quotient-orientation : (n : ℕ) →
    type-hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
      ( symmetric-Group
        ( quotient-sign-Set
          ( succ-ℕ (succ-ℕ n))
          ( pair
            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
  pr1 (hom-equiv-is-set-quotient-orientation n) p =
    pr1 (center (is-contr-equiv-orientation n p))
  pr2 (hom-equiv-is-set-quotient-orientation n) p q =
    ( inv (eq-cartier-delooping-sign-loop-equiv-is-set-quotient n (p ∙ q))) ∙
      ( ( preserves-mul-hom-Group
        ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
        ( symmetric-Group
          ( quotient-sign-Set
            ( succ-ℕ (succ-ℕ n))
            ( pair
              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
              ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
        ( comp-hom-Group
          ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
          ( loop-group-Set
            ( quotient-sign-Set
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
          ( symmetric-Group
            ( quotient-sign-Set
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
          ( hom-symmetric-group-loop-group-Set
            ( quotient-sign-Set
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
          ( cartier-delooping-sign-loop n))
        ( p)
        ( q) ∙
        ( ( ap
          ( mul-Group
            ( symmetric-Group
              ( quotient-sign-Set
                ( succ-ℕ (succ-ℕ n))
                ( pair
                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                  ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
            ( map-hom-Group
              ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
              ( symmetric-Group
                ( quotient-sign-Set (succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                    (unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
              ( comp-hom-Group
                ( loop-group-Set (raise-Set l (Fin-Set (succ-ℕ (succ-ℕ n)))))
                ( loop-group-Set
                  ( quotient-sign-Set
                    ( succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( symmetric-Group
                  ( quotient-sign-Set
                    ( succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( hom-symmetric-group-loop-group-Set
                  ( quotient-sign-Set
                    ( succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( cartier-delooping-sign-loop n))
              ( p)))
          ( eq-cartier-delooping-sign-loop-equiv-is-set-quotient n q)) ∙
          ( ap
            ( λ s →
              mul-Group
                ( symmetric-Group
                  ( quotient-sign-Set
                    ( succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( s)
                ( pr1 (center (is-contr-equiv-orientation n q))))
            ( eq-cartier-delooping-sign-loop-equiv-is-set-quotient n p)))))
```
