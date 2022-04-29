# Exclusive disjunction of propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.xor where

open import foundation.cartesian-product-types using (_×_)
open import foundation.conjunction using (conj-Prop)
open import foundation.coproduct-types using
  ( coprod; inl; inr; coprod-Prop; neq-inr-inl; neq-inl-inr)
open import foundation.decidable-propositions using
  ( decidable-Prop; prop-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-prod; is-decidable-neg)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation.empty-types using (ex-falso)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; inv-equiv; is-equiv; id-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-cartesian-product-types using (equiv-prod)
open import foundation.identity-types using (Id; tr; inv)
open import foundation.negation using (¬; neg-Prop; is-prop-neg)
open import foundation.propositional-extensionality using
  ( eq-equiv-Prop; eq-iff)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-Prop;
    is-prop-all-elements-equal; eq-is-prop; is-prop-prod; is-prop-is-prop;
    all-elements-equal; type-hom-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation.type-arithmetic-coproduct-types using
  ( right-distributive-Σ-coprod)
open import foundation.type-arithmetic-empty-type using
  (left-absorption-Σ; left-unit-law-coprod)
open import foundation.type-arithmetic-unit-type using (left-unit-law-Σ)
open import foundation.unit-type using (unit; star)
open import foundation.univalence using (eq-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.unordered-pairs using
  ( unordered-pair; standard-unordered-pair; element-unordered-pair;
    type-unordered-pair; 2-element-type-unordered-pair;
    other-element-unordered-pair; map-unordered-pair)

open import synthetic-homotopy-theory.commutative-operations using
  ( commutative-operation)

open import univalent-combinatorics.2-element-types using
  ( type-2-Element-Type; map-swap-2-Element-Type; compute-swap-2-Element-Type;
    compute-swap-Fin-two-ℕ)
open import univalent-combinatorics.equality-finite-types using
  ( has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  (Fin-UU-Fin; is-finite-type-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin)
```

## Idea

The exclusive disjunction of two propositions `P` and `Q` is the proposition that `P` holds and `Q` doesn't hold or `P` doesn't hold and `Q` holds.

## Definitions

### Exclusive disjunction of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor : UU (l1 ⊔ l2)
  xor = coprod (A × ¬ B) (¬ A × B)
```

### Exclusive disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  where

  xor-Prop : UU-Prop (l1 ⊔ l2)
  xor-Prop =
    coprod-Prop
      ( conj-Prop P (neg-Prop Q))
      ( conj-Prop (neg-Prop P) Q)
      ( λ p q → pr1 q (pr1 p))

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = type-Prop xor-Prop

  abstract
    is-prop-type-xor-Prop : is-prop type-xor-Prop
    is-prop-type-xor-Prop = is-prop-type-Prop xor-Prop
```

### The commutative operation of exclusive disjunction

```agda
predicate-commutative-xor :
  {l : Level} (p : unordered-pair (UU l)) → type-unordered-pair p → UU l
predicate-commutative-xor p x =
  ( element-unordered-pair p x) × (¬ (other-element-unordered-pair p x))

commutative-xor : {l : Level} → commutative-operation (UU l) (UU l)
commutative-xor p = Σ (type-unordered-pair p) (predicate-commutative-xor p)
```

### The commutative operation of exclusive disjunction of propositions

```agda
predicate-commutative-xor-Prop :
  {l : Level} (p : unordered-pair (UU-Prop l)) →
  type-unordered-pair p → UU l
predicate-commutative-xor-Prop p =
  predicate-commutative-xor (map-unordered-pair type-Prop p)

type-commutative-xor-Prop :
  {l : Level} → commutative-operation (UU-Prop l) (UU l)
type-commutative-xor-Prop p = commutative-xor (map-unordered-pair type-Prop p)

all-elements-equal-type-commutative-xor-Prop :
  {l : Level} (p : unordered-pair (UU-Prop l)) →
  all-elements-equal (type-commutative-xor-Prop p)
all-elements-equal-type-commutative-xor-Prop (pair X P) x y =
  cases-is-prop-type-commutative-xor-Prop
    ( has-decidable-equality-is-finite
      ( is-finite-type-UU-Fin-Level X)
      ( pr1 x)
      ( pr1 y))
  where
  cases-is-prop-type-commutative-xor-Prop :
    is-decidable (Id (pr1 x) (pr1 y)) → Id x y
  cases-is-prop-type-commutative-xor-Prop (inl p) =
    eq-pair-Σ
      ( p)
      ( eq-is-prop (is-prop-prod (is-prop-type-Prop (P (pr1 y))) is-prop-neg))
  cases-is-prop-type-commutative-xor-Prop (inr np) =
    ex-falso
      ( tr
        ( λ z → ¬ (type-Prop (P z)))
        ( compute-swap-2-Element-Type X (pr1 x) (pr1 y) np)
        ( pr2 (pr2 x))
        ( pr1 (pr2 y)))
        
is-prop-type-commutative-xor-Prop :
  {l : Level} (p : unordered-pair (UU-Prop l)) →
  is-prop (type-commutative-xor-Prop p)
is-prop-type-commutative-xor-Prop p =
  is-prop-all-elements-equal
    ( all-elements-equal-type-commutative-xor-Prop p)

commutative-xor-Prop :
  {l : Level} → commutative-operation (UU-Prop l) (UU-Prop l)
pr1 (commutative-xor-Prop E) = type-commutative-xor-Prop E 
pr2 (commutative-xor-Prop E) = is-prop-type-commutative-xor-Prop E
```

## Properties

### The commutative exclusive disjunction at a standard unordered pair

```agda
module _
  {l : Level} {A B : UU l}
  where
  
  xor-commutative-xor :
    commutative-xor (standard-unordered-pair A B) → xor A B
  xor-commutative-xor (pair (inl (inr star)) (pair p nq)) =
    inl
      ( pair p
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-two-ℕ zero-Fin)
          ( nq)))
  xor-commutative-xor (pair (inr star) (pair q np)) =
    inr
      ( pair
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-two-ℕ one-Fin)
          ( np))
        ( q))

  commutative-xor-xor :
    xor A B → commutative-xor (standard-unordered-pair A B)
  pr1 (commutative-xor-xor (inl (pair a nb))) = zero-Fin
  pr1 (pr2 (commutative-xor-xor (inl (pair a nb)))) = a
  pr2 (pr2 (commutative-xor-xor (inl (pair a nb)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-two-ℕ zero-Fin))
      ( nb)
  pr1 (commutative-xor-xor (inr (pair na b))) = one-Fin
  pr1 (pr2 (commutative-xor-xor (inr (pair na b)))) = b
  pr2 (pr2 (commutative-xor-xor (inr (pair na b)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-two-ℕ one-Fin))
      ( na)
```

```agda
xor-commutative-xor-Prop :
  {l : Level} (P Q : UU-Prop l) →
  type-hom-Prop
    ( commutative-xor-Prop (standard-unordered-pair P Q))
    ( xor-Prop P Q)
xor-commutative-xor-Prop P Q x =
  {!xor-commutative-xor (map-unordered-pair type-Prop (standard-unordered-pair P Q))!}

eq-commutative-xor-xor' :
  {l : Level} (P Q : UU-Prop l) →
  Id (commutative-xor-Prop (standard-unordered-pair P Q)) (xor-Prop P Q)
eq-commutative-xor-xor' P Q = eq-iff ϕ ψ
  where
  ϕ : type-Prop (commutative-xor-Prop (standard-unordered-pair P Q)) →
      type-Prop (xor-Prop P Q)
  ϕ (pair (inl (inr star)) u) = {!!}
  ϕ (pair (inr star) u) = {!!}
  ψ : type-Prop (xor-Prop P Q) →
      type-Prop (commutative-xor-Prop (standard-unordered-pair P Q))
  pr1 (ψ (inl (pair p nq))) = zero-Fin
  pr1 (pr2 (ψ (inl (pair p nq)))) = p
  pr2 (pr2 (ψ (inl (pair p nq)))) =
    tr ( λ t →
         ¬ (type-Prop (element-unordered-pair (standard-unordered-pair P Q) t)))
       ( inv (compute-swap-Fin-two-ℕ zero-Fin))
       ( nq)
  ψ (inr (pair np q)) = {!!}

eq-commmutative-xor-xor :
  {l : Level} (P Q : UU-Prop l) →
  Id (commutative-xor-Prop (standard-unordered-pair P Q)) (xor-Prop P Q)
eq-commmutative-xor-xor P Q =
  eq-equiv-Prop
    ( ( ( equiv-coprod
          ( ( ( left-unit-law-coprod (type-Prop (conj-Prop P (neg-Prop Q)))) ∘e
              ( equiv-coprod
                ( left-absorption-Σ
                  ( λ x →
                    ( type-Prop
                      ( pr2 (standard-unordered-pair P Q) (inl (inl x)))) ×
                      ( ¬ ( type-Prop
                            ( pr2
                              ( standard-unordered-pair P Q)
                              ( map-swap-2-Element-Type
                                ( pr1 (standard-unordered-pair P Q))
                                ( inl (inl x))))))))
                ( ( equiv-prod
                    ( id-equiv)
                    ( tr
                      ( λ b →
                        ( ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b))) ≃
                        ( ¬ (type-Prop Q)))
                      ( inv (compute-swap-Fin-two-ℕ zero-Fin))
                      ( id-equiv))) ∘e
                    ( left-unit-law-Σ
                      ( λ y →
                        ( type-Prop
                          ( pr2 (standard-unordered-pair P Q) (inl (inr y)))) ×
                        ( ¬ ( type-Prop
                              ( pr2
                                ( standard-unordered-pair P Q)
                                ( map-swap-2-Element-Type
                                  ( pr1 (standard-unordered-pair P Q))
                                  ( inl (inr y))))))))))) ∘e
          ( ( right-distributive-Σ-coprod
              ( Fin 0)
              ( unit)
              ( λ x →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inl x))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q)) (inl x)))))))))
        ( ( equiv-prod
            ( tr
              ( λ b →
                ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b)) ≃
                ¬ (type-Prop P))
              ( inv (compute-swap-Fin-two-ℕ one-Fin))
              ( id-equiv))
            ( id-equiv)) ∘e
          ( ( commutative-prod) ∘e
            ( left-unit-law-Σ
              ( λ y →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inr y))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q))
                          ( inr y)))))))))) ∘e
      ( right-distributive-Σ-coprod
        ( Fin 1)
        ( unit)
        ( λ x →
          ( type-Prop (pr2 (standard-unordered-pair P Q) x)) ×
          ( ¬ ( type-Prop
                ( pr2
                  ( standard-unordered-pair P Q)
                  ( map-swap-2-Element-Type
                    ( pr1 (standard-unordered-pair P Q))
                    ( x)))))))))
```

### Exclusive disjunction of decidable propositions

```agda
is-decidable-xor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (xor A B)
is-decidable-xor d e =
  is-decidable-coprod
    ( is-decidable-prod d (is-decidable-neg e))
    ( is-decidable-prod (is-decidable-neg d) e)

xor-decidable-Prop :
  {l1 l2 : Level} → decidable-Prop l1 → decidable-Prop l2 →
  decidable-Prop (l1 ⊔ l2)
pr1 (xor-decidable-Prop P Q) =
  type-xor-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr1 (pr2 (xor-decidable-Prop P Q)) =
  is-prop-type-xor-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr2 (pr2 (xor-decidable-Prop P Q)) =
  is-decidable-xor
    ( is-decidable-type-decidable-Prop P)
    ( is-decidable-type-decidable-Prop Q)
```

