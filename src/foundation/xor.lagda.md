# Exclusive disjunction of propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.xor where

open import foundation.cartesian-product-types using (_×_)
open import foundation.conjunction using (conj-Prop)
open import foundation.coproduct-types using (coprod; inl; inr; coprod-Prop; neq-inr-inl; neq-inl-inr)
open import foundation.decidable-propositions using
  ( decidable-Prop; prop-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-prod; is-decidable-neg)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation.empty-types using (ex-falso)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (_≃_; _∘e_; inv-equiv; is-equiv; id-equiv)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-cartesian-product-types using (equiv-prod)
open import foundation.identity-types using (Id; tr; inv)
open import foundation.negation using (¬; neg-Prop; is-prop-neg)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-Prop; is-prop-all-elements-equal;
    eq-is-prop; is-prop-prod; is-prop-is-prop)
open import foundation.propositional-truncations using (apply-universal-property-trunc-Prop)
open import foundation.type-arithmetic-cartesian-product-types using (commutative-prod)
open import foundation.type-arithmetic-coproduct-types using (right-distributive-Σ-coprod)
open import foundation.type-arithmetic-empty-type using
  (left-absorption-Σ; left-unit-law-coprod)
open import foundation.type-arithmetic-unit-type using (left-unit-law-Σ)
open import foundation.unit-type using (unit; star)
open import foundation.univalence using (eq-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.unordered-pairs using (unordered-pair; standard-unordered-pair)

open import univalent-combinatorics.2-element-types using
  ( type-2-Element-Type; map-swap-2-Element-Type; compute-swap-2-Element-Type)
open import univalent-combinatorics.equality-finite-types using
  ( has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  (Fin-UU-Fin; is-finite-type-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

The exclusive disjunction of two propositions `P` and `Q` is the proposition that `P` holds and `Q` doesn't hold or `P` doesn't hold and `Q` holds.

## Definition

```agda
xor-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
xor-Prop P Q =
  coprod-Prop (conj-Prop P (neg-Prop Q)) (conj-Prop (neg-Prop P) Q) (λ p q → pr1 q (pr1 p))

type-xor-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-xor-Prop P Q = type-Prop (xor-Prop P Q)

abstract
  is-prop-type-xor-Prop :
    {l1 l2 : Level} → (P : UU-Prop l1) → (Q : UU-Prop l2) →
    is-prop (type-xor-Prop P Q)
  is-prop-type-xor-Prop P Q =
    is-prop-type-Prop (xor-Prop P Q)

type-commutative-xor-Prop : {l : Level} → unordered-pair (UU-Prop l) → UU l
type-commutative-xor-Prop (pair X P) =
  Σ (type-2-Element-Type X) λ x → type-Prop (P x) × ¬ (type-Prop (P (map-swap-2-Element-Type X x)))

is-prop-type-commutative-xor-Prop : {l : Level} → (E : unordered-pair (UU-Prop l)) →
  is-prop (type-commutative-xor-Prop E)
is-prop-type-commutative-xor-Prop (pair X P) =
  is-prop-all-elements-equal
    ( λ x y →
      cases-is-prop-type-commutative-xor-Prop
        ( x)
        ( y)
        ( has-decidable-equality-is-finite (is-finite-type-UU-Fin-Level X) (pr1 x) (pr1 y)))
  where
  cases-is-prop-type-commutative-xor-Prop : (x y : type-commutative-xor-Prop (pair X P)) →
    is-decidable (Id (pr1 x) (pr1 y)) → Id x y
  cases-is-prop-type-commutative-xor-Prop x y (inl p) =
    eq-pair-Σ p (eq-is-prop (is-prop-prod (is-prop-type-Prop (P (pr1 y))) is-prop-neg))
  cases-is-prop-type-commutative-xor-Prop x y (inr np) =
    ex-falso
      ( tr
        ( λ z → ¬ (type-Prop (P z)))
        ( compute-swap-2-Element-Type X (pr1 x) (pr1 y) np)
        ( pr2 (pr2 x))
        ( pr1 (pr2 y)))

commutative-xor-Prop : {l : Level} → unordered-pair (UU-Prop l) → UU-Prop l
pr1 (commutative-xor-Prop E) = type-commutative-xor-Prop E 
pr2 (commutative-xor-Prop E) = is-prop-type-commutative-xor-Prop E

eq-commmutative-xor-xor : {l : Level} (P Q : UU-Prop l) →
  Id (commutative-xor-Prop (standard-unordered-pair P Q)) (xor-Prop P Q)
eq-commmutative-xor-xor P Q =
  eq-pair-Σ
    ( eq-equiv
      ( type-commutative-xor-Prop (standard-unordered-pair P Q))
      ( type-xor-Prop P Q)
      ( ( equiv-coprod
        ( ( left-unit-law-coprod (type-Prop (conj-Prop P (neg-Prop Q))) ∘e
                equiv-coprod
                  ( left-absorption-Σ
                    ( λ x →
                      type-Prop (pr2 (standard-unordered-pair P Q) (inl (inl x))) ×
                        ¬ (type-Prop
                          ( pr2
                            ( standard-unordered-pair P Q)
                            ( map-swap-2-Element-Type (pr1 (standard-unordered-pair P Q)) (inl (inl x)))))))
                  ( ( equiv-prod
                    ( id-equiv)
                    ( tr
                      ( λ b → ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b)) ≃ ¬ (type-Prop Q))
                      ( inv (compute-swap-2-Element-Type (Fin-UU-Fin 2) (inl (inr star)) (inr star) neq-inl-inr))
                      ( id-equiv))) ∘e
                    ( left-unit-law-Σ
                      ( λ y →
                        type-Prop (pr2 (standard-unordered-pair P Q) (inl (inr y))) ×
                          ¬ (type-Prop
                            ( pr2
                              ( standard-unordered-pair P Q)
                              ( map-swap-2-Element-Type (pr1 (standard-unordered-pair P Q)) (inl (inr y))))))))) ∘e
          ( ( right-distributive-Σ-coprod
            ( Fin 0)
            ( unit)
            ( λ x →
              type-Prop (pr2 (standard-unordered-pair P Q) (inl x)) ×
                ¬ (type-Prop
                  ( pr2
                    ( standard-unordered-pair P Q)
                    ( map-swap-2-Element-Type (pr1 (standard-unordered-pair P Q)) (inl x))))))))
        ( ( equiv-prod
          ( tr
            ( λ b → ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b)) ≃ ¬ (type-Prop P))
            ( inv (compute-swap-2-Element-Type (Fin-UU-Fin 2) (inr star) (inl (inr star)) neq-inr-inl))
            ( id-equiv))
          ( id-equiv) ∘e
          ( ( commutative-prod) ∘e
            ( left-unit-law-Σ
              ( λ y →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inr y))) ×
                  ¬ ( type-Prop
                    ( pr2
                      ( standard-unordered-pair P Q)
                      ( map-swap-2-Element-Type (pr1 (standard-unordered-pair P Q)) (inr y)))))))))) ∘e
        ( right-distributive-Σ-coprod
          ( Fin 1)
          ( unit)
          ( λ x →
            type-Prop (pr2 (standard-unordered-pair P Q) x) ×
            ¬ (type-Prop
              ( pr2
                ( standard-unordered-pair P Q)
                ( map-swap-2-Element-Type (pr1 (standard-unordered-pair P Q)) x)))))))
    ( eq-is-prop (is-prop-is-prop (type-xor-Prop P Q)))

xor-decidable-Prop :
  {l1 l2 : Level} → decidable-Prop l1 → decidable-Prop l2 →
  decidable-Prop (l1 ⊔ l2)
pr1 (xor-decidable-Prop P Q) =
  type-xor-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr1 (pr2 (xor-decidable-Prop P Q)) =
  is-prop-type-xor-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr2 (pr2 (xor-decidable-Prop P Q)) =
  is-decidable-coprod
    ( is-decidable-prod
      ( is-decidable-type-decidable-Prop P)
      ( is-decidable-neg (is-decidable-type-decidable-Prop Q)))
    ( is-decidable-prod
      ( is-decidable-neg (is-decidable-type-decidable-Prop P))
      ( is-decidable-type-decidable-Prop Q))
```

