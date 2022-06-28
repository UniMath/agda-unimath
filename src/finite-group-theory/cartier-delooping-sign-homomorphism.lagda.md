# Cartier's delooping of the sign homomorphism

```agda
{-# OPTIONS --without-K --exact-split --experimental-lossy-unification #-}

module finite-group-theory.cartier-delooping-sign-homomorphism where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import finite-group-theory.permutations using
  ( is-contr-parity-transposition-permutation; list-transpositions-permutation-count;
    retr-permutation-list-transpositions-count; is-generated-transposition-symmetric-Fin-Level)
open import finite-group-theory.sign-homomorphism using
  ( sign-homomorphism; eq-sign-homomorphism-transposition)
open import finite-group-theory.transpositions using
  ( permutation-list-transpositions; eq-concat-permutation-list-transpositions;
    is-transposition-permutation-Prop; transposition; two-elements-transposition;
    transposition-conjugation-equiv; is-involution-map-transposition;
    correct-transposition-conjugation-equiv-list; correct-transposition-conjugation-equiv;
    eq-equiv-universes-transposition)

open import foundation.automorphisms using (Aut)
open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-types using (is-contr; center; eq-is-contr)
open import foundation.coproduct-types using (inl; inr; neq-inr-inl)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.decidable-types using (is-decidable; is-prop-is-decidable)
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
    right-unit-law-equiv; htpy-eq-equiv; is-equiv-map-equiv; associative-comp-equiv)
open import foundation.equivalence-relations using
  ( Eq-Rel; refl-Eq-Rel; type-Eq-Rel; is-prop-type-Eq-Rel)
open import foundation.functions using (_∘_)
open import foundation.function-extensionality using (eq-htpy; htpy-eq)
open import foundation.functoriality-propositional-truncation using (map-trunc-Prop)
open import foundation.functoriality-set-quotients using
  ( unique-equiv-is-set-quotient; equiv-is-set-quotient;
    eq-equiv-eq-one-value-equiv-is-set-quotient)
open import foundation.empty-types using (ex-falso)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using
  ( Id; inv; _∙_; ap; refl; tr; ap-concat; distributive-inv-concat; inv-inv)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.involutions using (own-inverse-is-involution)
open import foundation.mere-equivalences using
  ( transitive-mere-equiv; symmetric-mere-equiv; mere-equiv; is-set-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop;
    all-elements-equal-type-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel; reflects-map-reflecting-map-Eq-Rel)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise; raise)
open import foundation.sets using
  ( is-set; Id-Prop; UU-Set; type-Set; is-set-type-Set; is-prop-is-set; is-set-equiv)
open import foundation.subuniverses using (is-one-type-UU-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.unit-type using (star)
open import foundation.univalence using (equiv-eq; eq-equiv)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient-large-set-quotient; is-effective-is-set-quotient)
open import foundation.universe-levels using (Level; lzero; lsuc; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using
  ( hom-Concrete-Group; classifying-type-Concrete-Group;
    abstract-group-Concrete-Group; hom-group-hom-Concrete-Group;
    map-hom-Concrete-Group)
open import group-theory.groups using
  ( set-Group; type-Group; mul-Group; semigroup-Group)
open import group-theory.homomorphisms-generated-subgroups using
  ( restriction-generating-subset-Group; eq-map-restriction-generating-subset-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; htpy-hom-Group; comp-hom-Group; map-hom-Group; preserves-mul-hom-Group;
    htpy-eq-hom-Group; id-hom-Group)
open import group-theory.homomorphisms-semigroups using (preserves-mul; is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using (hom-iso-Group; hom-inv-iso-Group)
open import group-theory.loop-groups-sets using
  ( loop-group-Set; map-hom-symmetric-group-loop-group-Set; hom-symmetric-group-loop-group-Set;
    map-hom-inv-symmetric-group-loop-group-Set; hom-inv-symmetric-group-loop-group-Set;
    is-retr-hom-inv-symmetric-group-loop-group-Set; is-sec-hom-inv-symmetric-group-loop-group-Set;
    iso-symmetric-group-loop-group-Set; commutative-inv-map-hom-symmetric-group-loop-group-Set)
open import group-theory.subgroups using (group-Subgroup)
open import group-theory.subgroups-generated-by-subsets-groups using
  ( is-generating-subset-Group; subgroup-subset-Group)
open import group-theory.symmetric-groups using
  ( symmetric-Group; iso-symmetric-group-abstract-automorphism-group-Set;
    hom-symmetric-group-equiv-Set; hom-inv-symmetric-group-equiv-Set;
    iso-symmetric-group-equiv-Set)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( 2-Element-Decidable-Subtype; standard-2-Element-Decidable-Subtype;
    equiv-universes-2-Element-Decidable-Subtype)
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
  ( quotient-sign; quotient-sign-Set; mere-equiv-fin-2-quotient-sign;
    orientation-Complete-Undirected-Graph; equiv-fin-2-quotient-sign-equiv-Fin;
    map-orientation-complete-undirected-graph-equiv;
    even-difference-orientation-Complete-Undirected-Graph;
    preserves-even-difference-orientation-complete-undirected-graph-equiv;
    preserves-id-equiv-orientation-complete-undirected-graph-equiv;
    equiv-fin-2-quotient-sign-count; orientation-complete-undirected-graph-equiv;
    orientation-aut-count; is-decidable-even-difference-orientation-Complete-Undirected-Graph;
    not-even-difference-orientation-aut-transposition-count)
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
        ( map-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
  pr2 (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p)) =
    map-trunc-Prop
      ( λ e →
        eq-pair-Σ
          ( eq-equiv
            ( type-Set (pr1 (map-cartier-delooping-sign (succ-ℕ (succ-ℕ n)) (pair X p))))
            ( type-Set (raise-Set (lsuc l) (Fin-Set 2)))
            ( equiv-raise (lsuc l) (Fin 2) ∘e inv-equiv e))
          ( eq-is-prop (is-prop-is-set (raise (lsuc l) (type-Set (Fin-Set 2))))))
      ( mere-equiv-fin-2-quotient-sign
        ( succ-ℕ (succ-ℕ n))
        ( pair
          ( type-Set X)
          ( map-trunc-Prop (λ p' → equiv-eq (inv (pr1 (pair-eq-Σ p'))) ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) p))
        ( star))

  abstract
    eq-fin-2-map-cartier-delooping-sign-count : (n : ℕ) →
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
    eq-fin-2-map-cartier-delooping-sign-count zero-ℕ X eX = refl
    eq-fin-2-map-cartier-delooping-sign-count (succ-ℕ zero-ℕ) X eX = refl
    eq-fin-2-map-cartier-delooping-sign-count (succ-ℕ (succ-ℕ n)) X eX =
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
                ( equiv-fin-2-quotient-sign-equiv-Fin
                  ( succ-ℕ (succ-ℕ n))
                  ( pair
                    ( raise l (type-Set (pair X (is-set-count (pair (succ-ℕ (succ-ℕ n)) eX)))))
                    ( map-trunc-Prop
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
      ( eq-fin-2-map-cartier-delooping-sign-count n (Fin n) id-equiv)

module _
  { l : Level}
  where

  private
    raise-UU-Fin-Fin : (n : ℕ) → UU-Fin-Level l n
    pr1 (raise-UU-Fin-Fin n) = raise l (Fin n)
    pr2 (raise-UU-Fin-Fin n) = unit-trunc-Prop (equiv-raise l (Fin n))

    raise-Fin-Set : (n : ℕ) → UU-Set l
    raise-Fin-Set n = raise-Set l (Fin-Set n)

    orientation-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n)))) →
      ( orientation-Complete-Undirected-Graph
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))) ≃
        orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
    orientation-loop-Fin n p =
      orientation-complete-undirected-graph-equiv
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( inv p))

    map-orientation-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n)))) →
      orientation-Complete-Undirected-Graph
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))) →
      orientation-Complete-Undirected-Graph
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
    map-orientation-loop-Fin n p =
      map-equiv (orientation-loop-Fin n p)

    quotient-sign-set-Fin : (n : ℕ) → UU-Set (lsuc l)
    quotient-sign-set-Fin n =
      quotient-sign-Set n (raise-UU-Fin-Fin n)

    quotient-map-even-difference-Fin : (n : ℕ) →
      ( orientation-Complete-Undirected-Graph n (raise-UU-Fin-Fin n)) →
      ( type-Set (quotient-sign-set-Fin n))
    quotient-map-even-difference-Fin n =
      quotient-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph n (raise-UU-Fin-Fin n))

    quotient-reflecting-map-even-difference-Fin : (n : ℕ) →
      reflecting-map-Eq-Rel
        ( even-difference-orientation-Complete-Undirected-Graph n (raise-UU-Fin-Fin n))
        ( type-Set (quotient-sign-set-Fin n))
    quotient-reflecting-map-even-difference-Fin n =
      quotient-reflecting-map-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph n (raise-UU-Fin-Fin n))

    orientation-aut-succ-succ-Fin : (n : ℕ) →
      type-Group (symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n)))) →
      orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
    orientation-aut-succ-succ-Fin n =
      orientation-aut-count 
        ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( star)

  map-cartier-delooping-sign-loop : (n : ℕ) (X Y : UU l) →
    (eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) (eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
    Id X Y →
    Id
      ( quotient-sign (succ-ℕ (succ-ℕ n)) (pair X eX))
      ( quotient-sign (succ-ℕ (succ-ℕ n)) (pair Y eY))
  map-cartier-delooping-sign-loop n X Y eX eY p =
    ap (quotient-sign (succ-ℕ (succ-ℕ n))) (eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))

  private
    map-cartier-delooping-sign-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n)))) →
      type-Group (loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
    map-cartier-delooping-sign-loop-Fin n =
      map-cartier-delooping-sign-loop n
        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))

  cartier-delooping-sign-loop : (n : ℕ) →
    type-hom-Group
      ( loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
      ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
  pr1 (cartier-delooping-sign-loop n) = map-cartier-delooping-sign-loop-Fin n
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
    ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
    coherence-square
      ( map-orientation-loop-Fin n p)
      ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-cartier-delooping-sign-loop-Fin n p)))
  coherence-square-map-cartier-delooping-sign-loop-Fin n p =
    coherence-square-map-cartier-delooping-sign-loop-Set n
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( p)
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( is-set-type-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
      ( is-set-type-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))

  private
    is-contr-equiv-orientation : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
      is-contr
        ( Σ
          ( type-Group
            ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
          ( λ h' →
            coherence-square
              ( map-orientation-loop-Fin n p)
              ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
              ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
              ( map-equiv h')))
    is-contr-equiv-orientation n p =
      unique-equiv-is-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
        ( is-set-quotient-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( is-set-quotient-large-set-quotient
          ( even-difference-orientation-Complete-Undirected-Graph
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( orientation-loop-Fin n p)
        ( λ {x} {y} →
          preserves-even-difference-orientation-complete-undirected-graph-equiv
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p))
            ( x)
            ( y))

  abstract
    eq-cartier-delooping-sign-loop-equiv-is-set-quotient : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
      Id 
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-cartier-delooping-sign-loop-Fin n p))
        ( pr1 (center (is-contr-equiv-orientation n p)))
    eq-cartier-delooping-sign-loop-equiv-is-set-quotient n p =
      ap pr1
        { x =
          pair
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
              ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
              ( map-cartier-delooping-sign-loop-Fin n p))
            ( coherence-square-map-cartier-delooping-sign-loop-Fin n p)}
        { y = center (is-contr-equiv-orientation n p)}
        ( eq-is-contr (is-contr-equiv-orientation n p))

  cases-map-orientation-even-difference-aut-Fin : (n : ℕ) →
    ( h : type-Group (symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
    is-decidable
      ( type-Eq-Rel
        ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( orientation-aut-succ-succ-Fin n h)
        ( map-orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( h)
          ( orientation-aut-succ-succ-Fin n h))) →
    type-Group
      ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
  cases-map-orientation-even-difference-aut-Fin n h (inl D) = id-equiv
  cases-map-orientation-even-difference-aut-Fin n h (inr ND) =
    ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
      ( star)
      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
      ( equiv-succ-Fin ∘e
        ( inv-equiv
          ( equiv-fin-2-quotient-sign-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
    
  map-orientation-even-difference-aut-Fin : (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n)))) → 
    type-Group
      ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
  map-orientation-even-difference-aut-Fin n h =
    cases-map-orientation-even-difference-aut-Fin n h
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( orientation-aut-succ-succ-Fin n h)
        ( map-orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( h)
          ( orientation-aut-succ-succ-Fin n h)))

  eq-map-orientation-even-difference-aut-fin-transposition : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l (raise l (Fin (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-orientation-even-difference-aut-Fin n (transposition Y))
      ( ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( star)
        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
        ( equiv-succ-Fin ∘e
          ( inv-equiv
            ( equiv-fin-2-quotient-sign-equiv-Fin
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( star)
              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
  eq-map-orientation-even-difference-aut-fin-transposition n Y =
    ap
      ( cases-map-orientation-even-difference-aut-Fin n (transposition Y))
      { x =
        is-decidable-even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( orientation-aut-succ-succ-Fin n (transposition Y))
          ( map-orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( transposition Y)
            ( orientation-aut-succ-succ-Fin n (transposition Y)))}
      { y =
        inr
          ( not-even-difference-orientation-aut-transposition-count
            ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( star)
            ( Y))}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-type-Eq-Rel
            ( even-difference-orientation-Complete-Undirected-Graph
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( orientation-aut-succ-succ-Fin n (transposition Y))
            ( map-orientation-complete-undirected-graph-equiv (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( transposition Y)
              ( orientation-aut-succ-succ-Fin n (transposition Y))))))

  cases-eq-map-orientation-even-difference-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
    ( D : is-decidable
      ( type-Eq-Rel
        ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( orientation-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p)))
        ( map-orientation-loop-Fin n p
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))) →
    ( k k' : Fin 2) →
    Id
      ( map-inv-equiv
        ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))
      ( k) →
    Id
      ( map-inv-equiv
        ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
          ( map-orientation-loop-Fin n p
            ( orientation-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( inv p))))))
      ( k') →
    Id
      ( map-equiv
        ( cases-map-orientation-even-difference-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p))
          ( D))
        ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))
      ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
        ( map-orientation-loop-Fin n p
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))
  cases-eq-map-orientation-even-difference-aut-Fin n p (inl D) k k' q r =
    reflects-map-reflecting-map-Eq-Rel
      ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
      ( D)
  cases-eq-map-orientation-even-difference-aut-Fin n p (inr ND) (inl (inr star)) (inl (inr star)) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( even-difference-orientation-Complete-Undirected-Graph
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
            ( reflects-map-reflecting-map-Eq-Rel
              ( even-difference-orientation-Complete-Undirected-Graph
                ( succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
              ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n))))
            ( is-set-quotient-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph
                ( succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( orientation-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( inv p)))
            ( map-orientation-loop-Fin n p
              ( orientation-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                  ( inv p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( q ∙ inv r))))
  cases-eq-map-orientation-even-difference-aut-Fin n p (inr ND) (inl (inr star)) (inr star) q r =
    ( ap
      ( map-equiv
        ( equiv-fin-2-quotient-sign-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( ( ap
        ( map-equiv equiv-succ-Fin)
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
              ( map-orientation-loop-Fin n p
                ( orientation-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                    ( inv p))))))
        ( right-inverse-law-equiv
          ( equiv-fin-2-quotient-sign-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  cases-eq-map-orientation-even-difference-aut-Fin n p (inr ND) (inr star) (inl (inr star)) q r =
    ( ap
      ( map-equiv
        ( equiv-fin-2-quotient-sign-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( ( ap
        ( map-equiv equiv-succ-Fin)
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
              ( map-orientation-loop-Fin n p
                ( orientation-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                    ( inv p))))))
        ( right-inverse-law-equiv
          ( equiv-fin-2-quotient-sign-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  cases-eq-map-orientation-even-difference-aut-Fin n p (inr ND) (inr star) (inr star) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( even-difference-orientation-Complete-Undirected-Graph
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
            ( reflects-map-reflecting-map-Eq-Rel
              ( even-difference-orientation-Complete-Undirected-Graph
                ( succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
              ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n))))
            ( is-set-quotient-large-set-quotient
              ( even-difference-orientation-Complete-Undirected-Graph
                ( succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( orientation-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( inv p)))
            ( map-orientation-loop-Fin n p
              ( orientation-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                  ( inv p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( q ∙ inv r))))

  eq-map-orientation-even-difference-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-equiv
        ( map-orientation-even-difference-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p)))
        ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))
      ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
        ( map-orientation-loop-Fin n p
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
              ( inv p)))))
  eq-map-orientation-even-difference-aut-Fin n p =
     cases-eq-map-orientation-even-difference-aut-Fin n p
      ( is-decidable-even-difference-orientation-Complete-Undirected-Graph
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( orientation-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p)))
        ( map-orientation-loop-Fin n p
          ( orientation-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p)))))
        ( map-inv-equiv
          ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
            ( orientation-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                ( inv p)))))
        ( map-inv-equiv
          ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( quotient-map-even-difference-Fin (succ-ℕ (succ-ℕ n))
            ( map-orientation-loop-Fin n p
              ( orientation-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n))) (inv p))))))
        ( refl)
        ( refl)

  eq-map-orientation-aut-loop-equiv-is-set-quotient : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) →
    Id 
      ( map-orientation-even-difference-aut-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( inv p)))
      ( pr1 (center (is-contr-equiv-orientation n p)))
  eq-map-orientation-aut-loop-equiv-is-set-quotient n p =
    eq-equiv-eq-one-value-equiv-is-set-quotient
      ( even-difference-orientation-Complete-Undirected-Graph (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-reflecting-map-even-difference-Fin (succ-ℕ (succ-ℕ n)))
      ( is-set-quotient-large-set-quotient
        ( even-difference-orientation-Complete-Undirected-Graph
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
      ( inv-equiv
        ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( map-orientation-loop-Fin n p)
      ( λ {x} {y} →
        preserves-even-difference-orientation-complete-undirected-graph-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p))
          ( x)
          ( y))
      ( map-equiv
        ( map-orientation-even-difference-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p))))
      ( orientation-aut-succ-succ-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( inv p)))
      ( eq-map-orientation-even-difference-aut-Fin n p)
      ( is-equiv-map-equiv (orientation-loop-Fin n p))
      ( is-equiv-map-equiv
        ( map-orientation-even-difference-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
            ( inv p))))


  eq-cartier-delooping-sign-loop-sign-homomorphism : {l' : Level} (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
        ( cartier-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
          ( comp-hom-Group
            ( symmetric-Group (Fin-Set 2))
            ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-inv-symmetric-group-loop-group-Set
              ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-symmetric-group-equiv-Set
              ( Fin-Set 2)
              ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
              ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( sign-homomorphism (succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  eq-cartier-delooping-sign-loop-sign-homomorphism n =
    map-inv-equiv
      ( equiv-ap-emb
        ( restriction-generating-subset-Group
          ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
          (is-transposition-permutation-Prop {l2 = l})
          ( tr
            ( λ s →
              is-generating-subset-Group
                ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s))
                ( is-transposition-permutation-Prop))
            ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( is-generated-transposition-symmetric-Fin-Level
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
          ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))))
      ( eq-htpy
        ( λ (pair f s) →
          apply-universal-property-trunc-Prop s
            ( Id-Prop
              ( set-Group (loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        (symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( cartier-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))))
                ( pair f s))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                    ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                      ( symmetric-Group (Fin-Set 2))
                      ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( comp-hom-Group
                        ( symmetric-Group (Fin-Set 2))
                        ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-inv-symmetric-group-loop-group-Set
                          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-symmetric-group-equiv-Set (Fin-Set 2)
                          ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
                          ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                      ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                        ( pair
                          ( Fin (succ-ℕ (succ-ℕ n)))
                          ( unit-trunc-Prop id-equiv))))
                    ( hom-inv-symmetric-group-equiv-Set
                      ( Fin-Set (succ-ℕ (succ-ℕ n)))
                      ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                      (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                ( pair f s)))
            ( λ (pair Y q) →
              ( eq-map-restriction-generating-subset-Group
                ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                ( is-transposition-permutation-Prop)
                ( tr
                  ( λ s₁ →
                     is-generating-subset-Group
                      ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                      ( is-transposition-permutation-Prop))
                  ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                  ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( cartier-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))))
                ( pair f s)) ∙
                ( ( htpy-eq-hom-Group
                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( id-hom-Group (loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-inv-symmetric-group-loop-group-Set
                      ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-symmetric-group-loop-group-Set
                      ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( inv
                    ( is-retr-hom-inv-symmetric-group-loop-group-Set
                      ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( ap (quotient-sign (succ-ℕ (succ-ℕ n)))
                    ( eq-pair-Σ
                     ( inv
                      ( eq-equiv
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( f)))
                     ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
                  ( ( ap
                    ( map-hom-Group
                      ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( hom-inv-symmetric-group-loop-group-Set
                        ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                    ( eq-cartier-delooping-sign-loop-equiv-is-set-quotient n
                      ( inv
                        ( eq-equiv
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( f))) ∙
                      ( inv
                        ( eq-map-orientation-aut-loop-equiv-is-set-quotient n
                          ( inv
                            ( eq-equiv
                              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                              ( f))))))) ∙
                    ( ap
                      ( λ g →
                        map-hom-Group
                          ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( map-orientation-even-difference-aut-Fin n g))
                      ( ( commutative-inv-map-hom-symmetric-group-loop-group-Set
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( map-hom-inv-symmetric-group-loop-group-Set
                            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                            ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                            ( f))
                          ( pr2 (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                          ( pr2 (raise-Fin-Set (succ-ℕ (succ-ℕ n))))) ∙
                          ( ap inv-equiv
                            ( ( htpy-eq-hom-Group
                              ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( comp-hom-Group
                                ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( loop-group-Set (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( hom-symmetric-group-loop-group-Set
                                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( hom-inv-symmetric-group-loop-group-Set
                                  ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))))
                              ( id-hom-Group
                                ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n)))))
                              ( is-sec-hom-inv-symmetric-group-loop-group-Set
                                ( raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( f)) ∙
                              ( inv q)))) ∙
                      ( ( ap
                        ( map-hom-Group
                          ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))))
                        ( ( ap
                          ( map-orientation-even-difference-aut-Fin n)
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition Y))) ∙
                          ( ( eq-map-orientation-even-difference-aut-fin-transposition n Y) ∙
                            ( ap
                              ( λ e →
                                ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                                  ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
                                  ( e ∘e
                                    ( inv-equiv
                                      ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                                        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                        ( star)
                                        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                              ( ( inv
                                ( eq-sign-homomorphism-transposition (succ-ℕ (succ-ℕ n))
                                  ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))
                                  ( map-equiv
                                    ( equiv-universes-2-Element-Decidable-Subtype
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( l)
                                      ( lzero))
                                    ( transposition-conjugation-equiv {l4 = l}
                                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                      ( Y))))) ∙
                                ( ap
                                  ( map-hom-Group
                                    ( symmetric-Group
                                      ( set-UU-Fin-Level
                                       ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                    ( symmetric-Group (Fin-Set 2))
                                    ( sign-homomorphism
                                      ( succ-ℕ (succ-ℕ n))
                                      ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                  ( ( inv
                                    ( eq-equiv-universes-transposition (Fin (succ-ℕ (succ-ℕ n)))
                                      ( l)
                                      ( lzero)
                                      ( transposition-conjugation-equiv
                                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                        ( Y)))) ∙
                                    ( ( eq-htpy-equiv
                                      ( correct-transposition-conjugation-equiv
                                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                        ( Y))) ∙
                                      ( ( associative-comp-equiv
                                        ( inv-equiv (inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                                        ( transposition Y)
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))) ∙
                                        ( ( ap
                                          ( λ e →
                                            inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) ∘e
                                              ( transposition Y ∘e e))
                                          ( inv-inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))) ∙
                                          ( ap
                                            ( λ e →
                                              inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) ∘e
                                                ( e ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                            ( q)))))))))))) ∙
                        ( inv
                          ( eq-map-restriction-generating-subset-Group
                            ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                            ( is-transposition-permutation-Prop)
                            ( tr
                              ( λ s₁ →
                                 is-generating-subset-Group
                                  ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                                  ( is-transposition-permutation-Prop))
                              ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                              ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                                ( pair
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                  ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                            ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                            ( comp-hom-Group
                              ( symmetric-Group (raise-Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                              ( comp-hom-Group
                                ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (Fin-Set 2))
                                ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                                ( comp-hom-Group
                                  ( symmetric-Group (Fin-Set 2))
                                  ( symmetric-Group (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( loop-group-Set (quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-inv-symmetric-group-loop-group-Set
                                    ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-symmetric-group-equiv-Set
                                    ( Fin-Set 2)
                                    ( quotient-sign-set-Fin (succ-ℕ (succ-ℕ n)))
                                    ( equiv-fin-2-quotient-sign-equiv-Fin (succ-ℕ (succ-ℕ n))
                                      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                                ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                                  ( pair
                                    ( Fin (succ-ℕ (succ-ℕ n)))
                                    ( unit-trunc-Prop id-equiv))))
                              ( hom-inv-symmetric-group-equiv-Set
                                ( Fin-Set (succ-ℕ (succ-ℕ n)))
                                ( raise-Fin-Set (succ-ℕ (succ-ℕ n)))
                                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                            ( pair f s))))))))))
```
