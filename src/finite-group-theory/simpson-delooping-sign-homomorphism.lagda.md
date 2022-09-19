---
title: Simpson's delooping of the sign homomorphism
---

```agda
{-# OPTIONS --without-K --experimental-lossy-unification #-}

module finite-group-theory.simpson-delooping-sign-homomorphism where

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.involutions
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
open import univalent-combinatorics.standard-finite-types
```

### Simpson's delooping of the sign homomorphism

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  sign-comp-Eq-Rel : Eq-Rel lzero (Fin n ≃ type-UU-Fin n X)
  pr1 sign-comp-Eq-Rel f g =
    Id-Prop (Fin-Set 2) (zero-Fin 1) (sign-homomorphism-Fin-two n X (f ∘e inv-equiv g))
  pr1 (pr2 sign-comp-Eq-Rel) {f} =
    ap pr1
      { x = pair (zero-Fin 1) (unit-trunc-Prop (pair nil (pair refl (right-inverse-law-equiv f))))}
      { y = center (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f))}
      ( eq-is-contr (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f)))
  pr1 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} P =
    ap pr1
      { x = pair (zero-Fin 1) (unit-trunc-Prop (pair nil (pair refl (left-inverse-law-equiv (f ∘e inv-equiv g)))))}
      { y = center (is-contr-parity-transposition-permutation n X (inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n X
          ( inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))) ∙
      ( ( preserves-add-sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)) (f ∘e inv-equiv g)) ∙
        ( ( ap
          ( add-Fin 2 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g))))
          ( inv P)) ∙
          ( ( ap
            ( λ k →
              mod-two-ℕ (add-ℕ (nat-Fin 2 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) k))
            ( is-zero-nat-zero-Fin {k = 1})) ∙
            ( ( issec-nat-Fin 1 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) ∙
              ( ap
                ( sign-homomorphism-Fin-two n X)
                ( ( distributive-inv-comp-equiv (inv-equiv g) f) ∙
                  ap (λ h → h ∘e inv-equiv f) (inv-inv-equiv g)))))))
  pr2 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} {h} P Q =
    ( ap mod-two-ℕ
      ( ( ap (add-ℕ zero-ℕ) (inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) Q)) ∙
        ( ap
          ( λ k → add-ℕ k (nat-Fin 2 (sign-homomorphism-Fin-two n X (g ∘e inv-equiv h))))
          ( inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) P)))) ∙
      ( ( inv
        ( preserves-add-sign-homomorphism-Fin-two n X (f ∘e inv-equiv g) (g ∘e inv-equiv h))) ∙
        ( ap
          ( sign-homomorphism-Fin-two n X)
          ( ( associative-comp-equiv (g ∘e inv-equiv h) (inv-equiv g) f) ∙
            ( ap
              ( λ h' → f ∘e h')
              ( ( inv (associative-comp-equiv (inv-equiv h) g (inv-equiv g))) ∙
                ( ( ap (λ h' → h' ∘e inv-equiv h) (left-inverse-law-equiv g)) ∙
                  ( left-unit-law-equiv (inv-equiv h))))))))
  quotient-sign-comp : UU (lsuc lzero ⊔ l)
  quotient-sign-comp = equivalence-class sign-comp-Eq-Rel

  quotient-sign-comp-Set : Set (lsuc lzero ⊔ l)
  quotient-sign-comp-Set = equivalence-class-Set sign-comp-Eq-Rel

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
                        ( has-decidable-equality-Fin (number-of-elements-count eX))
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
                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                ( pair
                  ( refl)
                  ( ( ap
                    ( λ e → equiv-count eX ∘e e)
                    ( distributive-inv-comp-equiv
                      ( transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-Fin (number-of-elements-count eX))
                          ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                      ( equiv-count eX))) ∙
                      ( ( ap
                        ( λ e → equiv-count eX ∘e (e ∘e inv-equiv (equiv-count eX)))
                        ( ( own-inverse-is-involution
                          ( is-involution-map-transposition
                            ( standard-2-Element-Decidable-Subtype
                              ( has-decidable-equality-Fin (number-of-elements-count eX))
                              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))) ∙
                          ( inv
                            ( right-unit-law-equiv
                              ( transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin (number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))) ∙
                          ( ( ap
                            ( λ h → equiv-count eX ∘e (h ∘e inv-equiv (equiv-count eX)))
                            ( ( right-unit-law-equiv
                              ( transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin (number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))) ∙
                              ( inv
                                ( right-unit-law-equiv
                                  ( transposition
                                    ( standard-2-Element-Decidable-Subtype
                                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
                            ( inv
                              ( associative-comp-equiv
                                ( inv-equiv (equiv-count eX))
                                ( permutation-list-transpositions
                                  ( in-list
                                    ( standard-2-Element-Decidable-Subtype
                                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                                ( equiv-count eX)) ∙
                              ( inv
                                ( eq-htpy-equiv
                                  ( correct-transposition-conjugation-equiv-list
                                    ( Fin (number-of-elements-count eX))
                                    ( X)
                                    ( equiv-count eX)
                                    ( in-list
                                      ( standard-2-Element-Decidable-Subtype
                                        ( has-decidable-equality-Fin (number-of-elements-count eX))
                                        ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))))))))))}
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
                        ( has-decidable-equality-Fin (number-of-elements-count eX))
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
                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))

  inv-Fin-2-quotient-sign-comp-count :
    ( T : quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( is-in-equivalence-class
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
    Fin 2
  inv-Fin-2-quotient-sign-comp-count T (inl P) = inl (inr star)
  inv-Fin-2-quotient-sign-comp-count T (inr NP) = inr star

  equiv-Fin-2-quotient-sign-comp-count : Fin 2 ≃
    quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
  pr1 equiv-Fin-2-quotient-sign-comp-count (inl (inr star)) =
    class
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX)
  pr1 equiv-Fin-2-quotient-sign-comp-count (inr star) =
    class
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX ∘e
        transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-Fin (number-of-elements-count eX))
            ( pr2 (pr2 ( two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
  pr2 equiv-Fin-2-quotient-sign-comp-count =
    is-equiv-has-inverse
      (λ T →
        inv-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ T →
        retr-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ k →
        sec-Fin-2-quotient-sign-comp-count k
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
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
      ¬ ( is-in-equivalence-class
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
      ( f : Fin (number-of-elements-count eX) ≃ X) →
      Id
        ( class
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
      is-in-equivalence-class
        ( sign-comp-Eq-Rel
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX ∘e
          transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-Fin
                (number-of-elements-count eX))
              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))    
    cases-retr-Fin-2-quotient-sign-comp-count T NP f p (inl (inr star)) q =
      ex-falso
        ( NP
          ( tr
            ( λ x →
              is-in-equivalence-class
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
          is-in-equivalence-class
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( x)
            ( equiv-count eX ∘e
              transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-Fin
                    (number-of-elements-count eX))
                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
        ( p)
        ( ( eq-mod-succ-cong-ℕ 1 0 2 (cong-zero-ℕ' 2)) ∙
          ( ( ap-add-Fin 2
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
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-Fin
                            ( number-of-elements-count eX))
                            ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
               ap
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( ( associative-comp-equiv
                  ( equiv-count eX ∘e
                    inv-equiv
                      ( equiv-count eX ∘e
                        transposition
                          ( standard-2-Element-Decidable-Subtype
                            (has-decidable-equality-Fin (number-of-elements-count eX))
                            ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                  ( inv-equiv (equiv-count eX))
                  ( f)) ∙
                  ( ap
                    ( λ h → f ∘e h)
                    ( inv
                      ( associative-comp-equiv
                        ( inv-equiv
                          ( equiv-count eX ∘e
                            transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin (number-of-elements-count eX))
                              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                        ( equiv-count eX)
                        ( inv-equiv (equiv-count eX))) ∙
                      ( ( ap
                        ( λ h →
                          h ∘e
                            inv-equiv
                              ( equiv-count eX ∘e
                                transposition
                                  ( standard-2-Element-Decidable-Subtype
                                    ( has-decidable-equality-Fin (number-of-elements-count eX))
                                    (pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                        ( left-inverse-law-equiv (equiv-count eX))) ∙
                        ( left-unit-law-equiv
                          ( inv-equiv
                            ( equiv-count eX ∘e
                              transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin (number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))))))))
    retr-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ( H : is-decidable
        (is-in-equivalence-class
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
              ( has-decidable-equality-Fin
                ( number-of-elements-count eX))
                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( pair
            ( is-in-equivalence-class
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin
                      ( number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
            ( is-prop-is-in-equivalence-class
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  (standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin
                      ( number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))
          ( λ (pair t p) →
            cases-retr-Fin-2-quotient-sign-comp-count T NP t
              ( inv
                ( eq-has-same-elements-equivalence-class
                  ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
                  ( T)
                  ( class
                    ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
                    ( t))
                  ( p)))
              ( sign-homomorphism-Fin-two
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( t ∘e inv-equiv (equiv-count eX)))
              ( refl)))
    sec-Fin-2-quotient-sign-comp-count : (k : Fin 2) →
      ( D : is-decidable
        ( is-in-equivalence-class
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
                 ap
                  ( sign-homomorphism-Fin-two
                    ( number-of-elements-count eX)
                    ( pair X (unit-trunc-Prop (equiv-count eX))))
                  ( ( associative-comp-equiv
                    ( inv-equiv (equiv-count eX))
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-Fin (number-of-elements-count eX))
                        ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                    ( equiv-count eX)) ∙
                    ( ap
                      ( λ h → equiv-count eX ∘e h)
                      ( ( ap
                        ( λ h → h ∘e inv-equiv (equiv-count eX))
                        { x =
                          transposition
                            (standard-2-Element-Decidable-Subtype
                              ( has-decidable-equality-Fin
                                ( number-of-elements-count eX))
                                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))}
                        ( inv
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin
                                  ( number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
                        ( inv
                          ( distributive-inv-comp-equiv
                            ( transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin
                                  ( number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                            ( equiv-count eX))))))))))
    sec-Fin-2-quotient-sign-comp-count (inr star) (inr ND) = refl

module _
  {l : Level} (n : ℕ) (X : UU-Fin l n) (ineq : leq-ℕ 2 n)
  where
  
  equiv-Fin-2-quotient-sign-comp-equiv-Fin-n : (h : Fin n ≃ type-UU-Fin n X) →
    ( Fin 2 ≃ quotient-sign-comp n X)
  equiv-Fin-2-quotient-sign-comp-equiv-Fin-n h =
    tr
      ( λ e → Fin 2 ≃ quotient-sign-comp n (pair (type-UU-Fin n X) e))
      ( all-elements-equal-type-trunc-Prop (unit-trunc-Prop (equiv-count (pair n h))) (pr2 X))
      ( equiv-Fin-2-quotient-sign-comp-count (pair n h) ineq)
    
  abstract
    mere-equiv-Fin-2-quotient-sign-comp :
      mere-equiv (Fin 2) (quotient-sign-comp n X)
    mere-equiv-Fin-2-quotient-sign-comp =
      map-trunc-Prop
        ( equiv-Fin-2-quotient-sign-comp-equiv-Fin-n)
        ( has-cardinality-type-UU-Fin n X)

module _
  { l : Level}
  where
  
  map-simpson-delooping-sign : (n : ℕ) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( Set l)
        ( raise-Set l (Fin-Set n))
        ( is-1-type-Set)) →
    classifying-type-Concrete-Group
      ( Automorphism-Group
        ( Set (lsuc lzero ⊔ l))
        ( raise-Set (lsuc lzero ⊔ l) (Fin-Set 2))
        ( is-1-type-Set))
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
      ( Automorphism-Group (Set l) (raise-Set l (Fin-Set n)) is-1-type-Set)
      ( Automorphism-Group
        ( Set (lsuc lzero ⊔ l))
        ( raise-Set (lsuc lzero ⊔ l) (Fin-Set 2))
        ( is-1-type-Set))
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
