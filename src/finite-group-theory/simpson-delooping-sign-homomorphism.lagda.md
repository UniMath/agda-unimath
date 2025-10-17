# Simpson's delooping of the sign homomorphism

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.simpson-delooping-sign-homomorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.action-on-equivalences-type-families-over-subuniverses
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-classes
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.symmetric-groups

open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Ideas

We give a definition of the delooping of the sign homomorphism based on a
suggestion by Alex Simpson.

## Definitions

```agda
module _
  {l : Level} (n : ℕ) (X : Type-With-Cardinality-ℕ l n)
  where

  sign-comp-equivalence-relation :
    equivalence-relation lzero (Fin n ≃ type-Type-With-Cardinality-ℕ n X)
  pr1 sign-comp-equivalence-relation f g =
    Id-Prop
      ( Fin-Set 2)
      ( zero-Fin 1)
      ( sign-homomorphism-Fin-2 n
        ( Fin-Type-With-Cardinality-ℕ n)
        ( inv-equiv f ∘e g))
  pr1 (pr2 sign-comp-equivalence-relation) f =
    ap pr1
      { x =
        zero-Fin 1 ,
        unit-trunc-Prop (nil , refl , left-inverse-law-equiv f)}
      { y =
        center
          ( is-contr-parity-transposition-permutation n
            (Fin-Type-With-Cardinality-ℕ n) (inv-equiv f ∘e f))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n
          (Fin-Type-With-Cardinality-ℕ n) (inv-equiv f ∘e f)))
  pr1 (pr2 (pr2 sign-comp-equivalence-relation)) f g P =
    ap pr1
      { x =
        zero-Fin 1 ,
        unit-trunc-Prop
          ( nil , refl , left-inverse-law-equiv (inv-equiv f ∘e g))}
      { y =
        center
          ( is-contr-parity-transposition-permutation n
            ( Fin-Type-With-Cardinality-ℕ n)
            ( inv-equiv (inv-equiv f ∘e g) ∘e (inv-equiv f ∘e g)))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n
          ( Fin-Type-With-Cardinality-ℕ n)
          ( inv-equiv (inv-equiv f ∘e g) ∘e (inv-equiv f ∘e g)))) ∙
      ( preserves-add-sign-homomorphism-Fin-2 n
        ( Fin-Type-With-Cardinality-ℕ n)
        ( inv-equiv (inv-equiv f ∘e g))
        ( inv-equiv f ∘e g) ∙
        ( ap
          ( add-Fin 2
            ( sign-homomorphism-Fin-2 n
              ( Fin-Type-With-Cardinality-ℕ n)
              ( inv-equiv (inv-equiv f ∘e g))))
          ( inv P) ∙
          ( ap
            ( mod-two-ℕ ∘
              ( nat-Fin 2
                ( sign-homomorphism-Fin-2 n
                  ( Fin-Type-With-Cardinality-ℕ n)
                  ( inv-equiv (inv-equiv f ∘e g)))) +ℕ_)
            ( is-zero-nat-zero-Fin {k = 1}) ∙
            ( is-section-nat-Fin 1
              ( sign-homomorphism-Fin-2 n
                ( Fin-Type-With-Cardinality-ℕ n)
                ( inv-equiv (inv-equiv f ∘e g))) ∙
              ( ap
                ( sign-homomorphism-Fin-2 n
                  ( Fin-Type-With-Cardinality-ℕ n))
                ( distributive-inv-comp-equiv g (inv-equiv f) ∙
                  ap (inv-equiv g ∘e_) (inv-inv-equiv f)))))))
  pr2 (pr2 (pr2 sign-comp-equivalence-relation)) f g h Q P =
    ( ap mod-two-ℕ
      ( ap
        ( zero-ℕ +ℕ_)
        ( inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) Q) ∙
        ( ap
          ( _+ℕ
            ( nat-Fin 2
              ( sign-homomorphism-Fin-2 n
                (Fin-Type-With-Cardinality-ℕ n) (inv-equiv g ∘e h))))
          ( inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) P)))) ∙
    ( inv
      ( preserves-add-sign-homomorphism-Fin-2 n
        ( Fin-Type-With-Cardinality-ℕ n)
        ( inv-equiv f ∘e g)
        ( inv-equiv g ∘e h)) ∙
      ( ap
        ( sign-homomorphism-Fin-2 n (Fin-Type-With-Cardinality-ℕ n))
        ( associative-comp-equiv (inv-equiv g ∘e h) g (inv-equiv f) ∙
          ( ap
            ( inv-equiv f ∘e_)
            ( inv (associative-comp-equiv h (inv-equiv g) g) ∙
              ( ap (_∘e h) (right-inverse-law-equiv g) ∙
                left-unit-law-equiv h))))))

  is-decidable-sign-comp-equivalence-relation :
    (f g : Fin n ≃ type-Type-With-Cardinality-ℕ n X) →
    is-decidable (sim-equivalence-relation sign-comp-equivalence-relation f g)
  is-decidable-sign-comp-equivalence-relation f g =
    has-decidable-equality-is-finite
      ( is-finite-Fin 2)
      ( zero-Fin 1)
      ( sign-homomorphism-Fin-2 n
        ( Fin-Type-With-Cardinality-ℕ n)
        ( inv-equiv f ∘e g))

  quotient-sign-comp : UU (lsuc lzero ⊔ l)
  quotient-sign-comp = equivalence-class sign-comp-equivalence-relation

  quotient-sign-comp-Set : Set (lsuc lzero ⊔ l)
  quotient-sign-comp-Set = equivalence-class-Set sign-comp-equivalence-relation

module _
  {l : Level} {X : UU l}
  (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  private
    transposition-eX : Fin (pr1 eX) ≃ Fin (pr1 eX)
    transposition-eX =
      transposition
        ( standard-2-Element-Decidable-Subtype
          ( has-decidable-equality-Fin (number-of-elements-count eX))
          ( pr2
            ( pr2
              ( two-distinct-elements-leq-2-Fin
                ( number-of-elements-count eX)
                ( ineq)))))

  private abstract
    lemma :
      Id
        ( inr star)
        ( sign-homomorphism-Fin-2
          ( number-of-elements-count eX)
          ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX))
          ( inv-equiv (equiv-count eX) ∘e (equiv-count eX ∘e transposition-eX)))
    lemma =
      ( inv
        ( eq-sign-homomorphism-Fin-2-transposition
          ( number-of-elements-count eX)
          ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-Fin (number-of-elements-count eX))
            ( pr2
              ( pr2
                ( two-distinct-elements-leq-2-Fin
                  (number-of-elements-count eX) (ineq))))))) ∙
        ( ap
          ( sign-homomorphism-Fin-2
            ( number-of-elements-count eX)
            ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX)))
          ( inv (left-unit-law-equiv transposition-eX) ∙
            ( ap
              ( _∘e transposition-eX)
              ( inv (left-inverse-law-equiv (equiv-count eX))) ∙
              ( associative-comp-equiv
                ( transposition-eX)
                ( equiv-count eX)
                ( inv-equiv (equiv-count eX))))))

  not-sign-comp-transposition-count :
    ( Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( sim-equivalence-relation
      ( sign-comp-equivalence-relation
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX)))
      ( transposition Y ∘e equiv-count eX)
      ( transposition Y ∘e (transposition Y ∘e equiv-count eX)))
  not-sign-comp-transposition-count Y P =
    neq-inl-inr
      ( P ∙
        ( ap
          ( sign-homomorphism-Fin-2
            ( number-of-elements-count eX)
            ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX)))
          ( ap
            ( inv-equiv (transposition Y ∘e equiv-count eX) ∘e_)
            ( inv
              ( associative-comp-equiv
                (equiv-count eX) (transposition Y) (transposition Y)) ∙
              ( ap
                ( _∘e equiv-count eX)
                ( eq-htpy-equiv (is-involution-map-transposition Y)) ∙
                ( left-unit-law-equiv (equiv-count eX)))) ∙
            ( ap
              ( _∘e equiv-count eX)
              ( distributive-inv-comp-equiv
                (equiv-count eX) (transposition Y)) ∙
              ( associative-comp-equiv
                ( equiv-count eX)
                ( inv-equiv (transposition Y))
                ( inv-equiv (equiv-count eX)) ∙
                ( ap
                  ( λ h → inv-equiv (equiv-count eX) ∘e (h ∘e equiv-count eX))
                  ( own-inverse-is-involution
                    ( is-involution-map-transposition Y)) ∙
                  ( ap
                    ( λ h →
                      inv-equiv (equiv-count eX) ∘e (transposition Y ∘e h))
                    ( inv (inv-inv-equiv (equiv-count eX)))))))) ∙
          ( preserves-conjugation-sign-homomorphism-Fin-2
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX))
            ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX))
            ( transposition Y)
            ( inv-equiv (equiv-count eX)) ∙
            ( eq-sign-homomorphism-Fin-2-transposition
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX))
              ( Y)))))

  inv-Fin-2-quotient-sign-comp-count :
    ( T : quotient-sign-comp
      ( number-of-elements-count eX)
      ( X , unit-trunc-Prop (equiv-count eX))) →
    is-decidable
      ( is-in-equivalence-class
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( T)
        ( equiv-count eX)) →
    Fin 2
  inv-Fin-2-quotient-sign-comp-count T (inl P) = inl (inr star)
  inv-Fin-2-quotient-sign-comp-count T (inr NP) = inr star

  equiv-Fin-2-quotient-sign-comp-count :
    Fin 2 ≃
    quotient-sign-comp
      ( number-of-elements-count eX)
      ( X , unit-trunc-Prop (equiv-count eX))
  pr1 equiv-Fin-2-quotient-sign-comp-count (inl (inr star)) =
    class
      ( sign-comp-equivalence-relation
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX)))
      ( equiv-count eX)
  pr1 equiv-Fin-2-quotient-sign-comp-count (inr star) =
    class
      ( sign-comp-equivalence-relation
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX)))
      ( equiv-count eX ∘e transposition-eX)
  pr2 equiv-Fin-2-quotient-sign-comp-count =
    is-equiv-is-invertible
      ( λ T →
        inv-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-2
                  ( number-of-elements-count eX)
                  ( Fin-Type-With-Cardinality-ℕ
                    ( number-of-elements-count eX))
                  ( inv-equiv a ∘e b)))
            ( T)
            ( equiv-count eX)))
      ( λ T →
        retraction-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-2
                  ( number-of-elements-count eX)
                  ( Fin-Type-With-Cardinality-ℕ
                    ( number-of-elements-count eX))
                  ( inv-equiv a ∘e b)))
            ( T)
            ( equiv-count eX)))
      ( λ k →
        section-Fin-2-quotient-sign-comp-count k
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-2
                  ( number-of-elements-count eX)
                  ( Fin-Type-With-Cardinality-ℕ
                    ( number-of-elements-count eX))
                  ( inv-equiv a ∘e b)))
            ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
            ( equiv-count eX)))
    where
    cases-retraction-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX))) →
      ¬ ( is-in-equivalence-class
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( T)
        ( equiv-count eX)) →
      ( f : Fin (number-of-elements-count eX) ≃ X) →
      Id
        ( class
          ( sign-comp-equivalence-relation
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX)))
          ( f))
        ( T) →
      ( k : Fin 2) →
      Id
        ( k)
        ( sign-homomorphism-Fin-2
          ( number-of-elements-count eX)
          ( Fin-Type-With-Cardinality-ℕ (number-of-elements-count eX))
          ( inv-equiv f ∘e equiv-count eX)) →
      is-in-equivalence-class
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( T)
        ( equiv-count eX ∘e transposition-eX)
    cases-retraction-Fin-2-quotient-sign-comp-count
      T NP f p (inl (inr star)) q =
      ex-falso
        ( NP
          ( tr
            ( λ x →
              is-in-equivalence-class
                ( sign-comp-equivalence-relation
                  ( number-of-elements-count eX)
                  ( X , unit-trunc-Prop (equiv-count eX)))
                ( x)
                ( equiv-count eX))
            ( p)
            ( q)))
    cases-retraction-Fin-2-quotient-sign-comp-count T NP f p (inr star) q =
      tr
        ( λ x →
          is-in-equivalence-class
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( x)
            ( equiv-count eX ∘e transposition-eX))
        ( p)
        ( eq-mod-succ-cong-ℕ 1 0 2 (cong-zero-ℕ' 2) ∙
          ( ap-add-Fin 2 q lemma ∙
            ( inv
              ( preserves-add-sign-homomorphism-Fin-2
                ( number-of-elements-count eX)
                ( Fin-Type-With-Cardinality-ℕ
                  ( number-of-elements-count eX))
                ( inv-equiv f ∘e equiv-count eX)
                ( inv-equiv (equiv-count eX) ∘e
                  ( equiv-count eX ∘e transposition-eX))) ∙
              ( ap
                ( sign-homomorphism-Fin-2
                  ( number-of-elements-count eX)
                  ( Fin-Type-With-Cardinality-ℕ
                    ( number-of-elements-count eX)))
                ( associative-comp-equiv
                  ( inv-equiv (equiv-count eX) ∘e
                    ( equiv-count eX ∘e transposition-eX))
                  ( equiv-count eX)
                  ( inv-equiv f) ∙
                  ( ap
                    ( λ h → inv-equiv f ∘e (equiv-count eX ∘e h))
                    ( inv
                      ( associative-comp-equiv
                        ( transposition-eX)
                        ( equiv-count eX)
                        ( inv-equiv (equiv-count eX))) ∙
                      ( ap
                        ( _∘e transposition-eX)
                        ( left-inverse-law-equiv (equiv-count eX)) ∙
                        ( left-unit-law-equiv transposition-eX)))))))))
    retraction-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( X , unit-trunc-Prop (equiv-count eX))) →
      ( H : is-decidable
        ( is-in-equivalence-class
          ( sign-comp-equivalence-relation
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX)))
          ( T)
          ( equiv-count eX))) →
      Id
        ( pr1 equiv-Fin-2-quotient-sign-comp-count
          ( inv-Fin-2-quotient-sign-comp-count T H))
        ( T)
    retraction-Fin-2-quotient-sign-comp-count T (inl P) =
      eq-effective-quotient'
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( equiv-count eX)
        ( T)
        ( P)
    retraction-Fin-2-quotient-sign-comp-count T (inr NP) =
      eq-effective-quotient'
        ( sign-comp-equivalence-relation
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX)))
        ( equiv-count eX ∘e transposition-eX)
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( is-in-equivalence-class-Prop
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( T)
            ( equiv-count eX ∘e transposition-eX))
          ( λ (t , p) →
            cases-retraction-Fin-2-quotient-sign-comp-count T NP t
              ( inv
                ( eq-has-same-elements-equivalence-class
                  ( sign-comp-equivalence-relation
                    ( number-of-elements-count eX)
                    ( X , unit-trunc-Prop (equiv-count eX)))
                  ( T)
                  ( class
                    ( sign-comp-equivalence-relation
                      ( number-of-elements-count eX)
                      ( X , unit-trunc-Prop (equiv-count eX)))
                    ( t))
                  ( p)))
              ( sign-homomorphism-Fin-2
                ( number-of-elements-count eX)
                ( Fin-Type-With-Cardinality-ℕ
                  ( number-of-elements-count eX))
                ( inv-equiv t ∘e equiv-count eX))
              ( refl)))
    section-Fin-2-quotient-sign-comp-count :
      ( k : Fin 2) →
      ( D : is-decidable
        ( is-in-equivalence-class
          ( sign-comp-equivalence-relation
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX)))
          ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
          ( equiv-count eX))) →
      Id
        ( inv-Fin-2-quotient-sign-comp-count
          (pr1 equiv-Fin-2-quotient-sign-comp-count k) (D))
        ( k)
    section-Fin-2-quotient-sign-comp-count (inl (inr star)) (inl D) = refl
    section-Fin-2-quotient-sign-comp-count (inl (inr star)) (inr ND) =
      ex-falso
        ( ND
          ( refl-equivalence-relation
            ( sign-comp-equivalence-relation
              ( number-of-elements-count eX)
              ( X , unit-trunc-Prop (equiv-count eX)))
            ( pr2 eX)))
    section-Fin-2-quotient-sign-comp-count (inr star) (inl D) =
      ex-falso
        ( neq-inr-inl
          ( lemma ∙
            ( inv
              ( D ∙
                ( ap
                  ( sign-homomorphism-Fin-2
                    ( number-of-elements-count eX)
                    ( Fin-Type-With-Cardinality-ℕ
                      ( number-of-elements-count eX)))
                  ( ap
                    ( _∘e equiv-count eX)
                    ( distributive-inv-comp-equiv
                      ( transposition-eX)
                      ( equiv-count eX)) ∙
                    ( associative-comp-equiv
                      ( equiv-count eX)
                      ( inv-equiv (equiv-count eX))
                      ( inv-equiv transposition-eX) ∙
                      ( ap
                        ( inv-equiv transposition-eX ∘e_)
                        ( left-inverse-law-equiv (equiv-count eX)) ∙
                        ( right-unit-law-equiv (inv-equiv transposition-eX) ∙
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin
                                  ( number-of-elements-count eX))
                                ( pr2
                                  ( pr2
                                    ( two-distinct-elements-leq-2-Fin
                                      ( number-of-elements-count eX)
                                      ( ineq)))))) ∙
                            ( inv (left-unit-law-equiv transposition-eX) ∙
                              ( ap
                                  ( _∘e transposition-eX)
                                  ( inv
                                    ( left-inverse-law-equiv
                                      ( equiv-count eX))) ∙
                                ( associative-comp-equiv
                                  ( transposition-eX)
                                  ( equiv-count eX)
                                  ( inv-equiv (equiv-count eX)))))))))))))))
    section-Fin-2-quotient-sign-comp-count (inr star) (inr ND) = refl

module _
  {l : Level} (n : ℕ) (X : Type-With-Cardinality-ℕ l n) (ineq : leq-ℕ 2 n)
  where

  equiv-fin-2-quotient-sign-comp-equiv-Fin :
    ( Fin n ≃ type-Type-With-Cardinality-ℕ n X) →
    ( Fin 2 ≃ quotient-sign-comp n X)
  equiv-fin-2-quotient-sign-comp-equiv-Fin h =
    tr
      ( λ e →
        Fin 2 ≃
        quotient-sign-comp n (type-Type-With-Cardinality-ℕ n X , e))
      ( all-elements-equal-type-trunc-Prop
        ( unit-trunc-Prop (equiv-count (n , h))) (pr2 X))
      ( equiv-Fin-2-quotient-sign-comp-count (n , h) ineq)
```

```agda
module _
  {l : Level} (n : ℕ)
  where

  map-simpson-comp-equiv :
    (X X' : Type-With-Cardinality-ℕ l n) →
    ( type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
    ( Fin n ≃ type-Type-With-Cardinality-ℕ n X) →
    ( Fin n ≃ type-Type-With-Cardinality-ℕ n X')
  map-simpson-comp-equiv X X' e f = e ∘e f

  simpson-comp-equiv :
    (X X' : Type-With-Cardinality-ℕ l n) →
    ( type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
    ( Fin n ≃ type-Type-With-Cardinality-ℕ n X) ≃
    ( Fin n ≃ type-Type-With-Cardinality-ℕ n X')
  pr1 (simpson-comp-equiv X X' e) = map-simpson-comp-equiv X X' e
  pr2 (simpson-comp-equiv X X' e) =
    is-equiv-is-invertible
      ( map-simpson-comp-equiv X' X (inv-equiv e))
      ( λ f →
        ( inv (associative-comp-equiv f (inv-equiv e) e)) ∙
        ( ap (_∘e f) (right-inverse-law-equiv e) ∙ left-unit-law-equiv f))
      ( λ f →
        ( inv (associative-comp-equiv f e (inv-equiv e))) ∙
        ( ap (_∘e f) (left-inverse-law-equiv e) ∙ left-unit-law-equiv f))

  abstract
    preserves-id-equiv-simpson-comp-equiv :
      (X : Type-With-Cardinality-ℕ l n) →
      Id (simpson-comp-equiv X X id-equiv) id-equiv
    preserves-id-equiv-simpson-comp-equiv X =
      eq-htpy-equiv left-unit-law-equiv

    preserves-comp-simpson-comp-equiv :
      ( X Y Z : Type-With-Cardinality-ℕ l n)
      ( e :
        type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n Y) →
      ( f :
        type-Type-With-Cardinality-ℕ n Y ≃ type-Type-With-Cardinality-ℕ n Z) →
      Id
        ( simpson-comp-equiv X Z (f ∘e e))
        ( simpson-comp-equiv Y Z f ∘e simpson-comp-equiv X Y e)
    preserves-comp-simpson-comp-equiv X Y Z e f =
      eq-htpy-equiv
        ( λ h → associative-comp-equiv h e f)

  private
    lemma-sign-comp :
      ( X X' : Type-With-Cardinality-ℕ l n)
      ( e :
        type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X')
      ( f f' : Fin n ≃ type-Type-With-Cardinality-ℕ n X) →
      Id
        ( sign-homomorphism-Fin-2 n
          ( Fin-Type-With-Cardinality-ℕ n)
          ( inv-equiv f ∘e f'))
        ( sign-homomorphism-Fin-2 n (Fin-Type-With-Cardinality-ℕ n)
          ( inv-equiv ( map-simpson-comp-equiv X X' e f) ∘e
            map-simpson-comp-equiv X X' e f'))
    lemma-sign-comp X X' e f f' =
      ap
        ( sign-homomorphism-Fin-2 n (Fin-Type-With-Cardinality-ℕ n))
        ( ap
          ( inv-equiv f ∘e_)
          ( inv (left-unit-law-equiv f') ∙
            ( ap (_∘e f') (inv (left-inverse-law-equiv e)) ∙
              ( associative-comp-equiv f' e (inv-equiv e)))) ∙
          ( ( inv
              ( associative-comp-equiv (e ∘e f') (inv-equiv e) (inv-equiv f))) ∙
            ( ap
              ( _∘e map-simpson-comp-equiv X X' e f')
              ( inv (distributive-inv-comp-equiv f e)))))

  preserves-sign-comp-simpson-comp-equiv :
    ( X X' : Type-With-Cardinality-ℕ l n)
    ( e :
      type-Type-With-Cardinality-ℕ n X ≃ type-Type-With-Cardinality-ℕ n X') →
    ( f f' : Fin n ≃ type-Type-With-Cardinality-ℕ n X) →
    ( sim-equivalence-relation (sign-comp-equivalence-relation n X) f f' ↔
      sim-equivalence-relation
        ( sign-comp-equivalence-relation n X')
        ( map-simpson-comp-equiv X X' e f)
        ( map-simpson-comp-equiv X X' e f'))
  pr1 (preserves-sign-comp-simpson-comp-equiv X X' e f f') =
    _∙ lemma-sign-comp X X' e f f'
  pr2 (preserves-sign-comp-simpson-comp-equiv X X' e f f') =
    _∙ inv (lemma-sign-comp X X' e f f')
```

```agda
module _
  {l : Level}
  where

  sign-comp-aut-succ-succ-Fin :
    (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l (n +ℕ 2))) →
    Fin (n +ℕ 2) ≃ raise l (Fin (n +ℕ 2))
  sign-comp-aut-succ-succ-Fin n = _∘e compute-raise l (Fin (n +ℕ 2))

  not-action-equiv-family-on-subuniverse-transposition :
    ( n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l
      ( raise-Fin l (n +ℕ 2))) →
    ¬ ( sim-equivalence-relation
      ( sign-comp-equivalence-relation (n +ℕ 2)
        ( raise-Fin l (n +ℕ 2) ,
          unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2))))
      ( sign-comp-aut-succ-succ-Fin n (transposition Y))
      ( map-equiv
        ( action-equiv-family-over-subuniverse
          ( mere-equiv-Prop (Fin (n +ℕ 2)))
          ( λ X → Fin (n +ℕ 2) ≃ pr1 X)
          ( raise l (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
          ( raise l (Fin (n +ℕ 2)) ,
            unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
          ( transposition Y))
        ( sign-comp-aut-succ-succ-Fin n (transposition Y))))
  not-action-equiv-family-on-subuniverse-transposition n =
    tr
      ( λ f →
        ( Y : 2-Element-Decidable-Subtype l
          ( raise-Fin l (n +ℕ 2))) →
            ¬ ( sim-equivalence-relation
              ( sign-comp-equivalence-relation
                ( n +ℕ 2)
                ( raise-Fin l (n +ℕ 2) ,
                  unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2))))
              ( sign-comp-aut-succ-succ-Fin n (transposition Y))
              ( map-equiv
                ( f
                  ( raise l (Fin (n +ℕ 2)) ,
                    unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
                  ( raise l (Fin (n +ℕ 2)) ,
                    unit-trunc-Prop (compute-raise-Fin l (n +ℕ 2)))
                  ( transposition Y))
                ( sign-comp-aut-succ-succ-Fin n (transposition Y)))))
      ( ap pr1
        { x =
          simpson-comp-equiv (n +ℕ 2) ,
          preserves-id-equiv-simpson-comp-equiv (n +ℕ 2)}
        { y =
          ( action-equiv-family-over-subuniverse
            ( mere-equiv-Prop (Fin (n +ℕ 2)))
            ( λ X →
              Fin (n +ℕ 2) ≃ type-Type-With-Cardinality-ℕ (n +ℕ 2) X) ,
            ( compute-id-equiv-action-equiv-family-over-subuniverse
              ( mere-equiv-Prop (Fin (n +ℕ 2)))
              ( λ X →
                Fin (n +ℕ 2) ≃ type-Type-With-Cardinality-ℕ (n +ℕ 2) X)))}
        ( eq-is-contr
          ( is-contr-equiv' _
            ( distributive-Π-Σ)
            ( is-contr-Π
              ( unique-action-equiv-family-over-subuniverse
                  ( mere-equiv-Prop (Fin (n +ℕ 2)))
                  ( λ Y →
                    Fin (n +ℕ 2) ≃
                    type-Type-With-Cardinality-ℕ (n +ℕ 2) Y))))))
      ( not-sign-comp-transposition-count
        (n +ℕ 2 , (compute-raise l (Fin (n +ℕ 2)))) (star))

  simpson-delooping-sign :
    (n : ℕ) →
    hom-Concrete-Group
      ( Type-With-Cardinality-ℕ-Concrete-Group l n)
      ( Type-With-Cardinality-ℕ-Concrete-Group (lsuc lzero ⊔ l) 2)
  simpson-delooping-sign =
    quotient-delooping-sign
      ( λ n X → Fin n ≃ type-Type-With-Cardinality-ℕ n X)
      ( sign-comp-equivalence-relation)
      ( λ n _ → is-decidable-sign-comp-equivalence-relation n)
      ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
      ( sign-comp-aut-succ-succ-Fin)
      ( not-action-equiv-family-on-subuniverse-transposition)

  eq-simpson-delooping-sign-homomorphism :
    (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (n +ℕ 2)))
        ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group (lsuc lzero ⊔ l) 2)
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
          ( Type-With-Cardinality-ℕ-Group l (n +ℕ 2))
          ( Type-With-Cardinality-ℕ-Group (lsuc lzero ⊔ l) 2)
          ( hom-group-hom-Concrete-Group
            ( Type-With-Cardinality-ℕ-Concrete-Group l (n +ℕ 2))
            ( Type-With-Cardinality-ℕ-Concrete-Group (lsuc lzero ⊔ l) 2)
            ( simpson-delooping-sign (n +ℕ 2)))
          ( hom-inv-iso-Group
            ( Type-With-Cardinality-ℕ-Group l (n +ℕ 2))
            ( loop-group-Set (raise-Fin-Set l (n +ℕ 2)))
            ( iso-loop-group-fin-Type-With-Cardinality-ℕ-Group l (n +ℕ 2))))
        ( hom-inv-symmetric-group-loop-group-Set (raise-Fin-Set l (n +ℕ 2))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (n +ℕ 2)))
        ( symmetric-Group (Fin-Set (n +ℕ 2)))
        ( Type-With-Cardinality-ℕ-Group (lsuc lzero ⊔ l) 2)
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (n +ℕ 2)))
          ( symmetric-Group (Fin-Set 2))
          ( Type-With-Cardinality-ℕ-Group (lsuc lzero ⊔ l) 2)
          ( symmetric-abstract-type-with-cardinality-ℕ-group-quotient-hom
            ( λ n X → Fin n ≃ type-Type-With-Cardinality-ℕ n X)
            ( sign-comp-equivalence-relation)
            ( λ n H → is-decidable-sign-comp-equivalence-relation n)
            ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
            ( sign-comp-aut-succ-succ-Fin)
            ( not-action-equiv-family-on-subuniverse-transposition)
            ( n))
          ( sign-homomorphism
            ( n +ℕ 2)
            ( Fin (n +ℕ 2) , unit-trunc-Prop id-equiv)))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (n +ℕ 2))
          ( raise-Fin-Set l (n +ℕ 2))
          ( compute-raise l (Fin (n +ℕ 2)))))
  eq-simpson-delooping-sign-homomorphism =
    eq-quotient-delooping-sign-homomorphism
      ( λ n X → Fin n ≃ type-Type-With-Cardinality-ℕ n X)
      ( sign-comp-equivalence-relation)
      ( λ n _ → is-decidable-sign-comp-equivalence-relation n)
      ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
      ( sign-comp-aut-succ-succ-Fin)
      ( not-action-equiv-family-on-subuniverse-transposition)
```

## References

{{#bibliography}} {{#reference MR23}}
