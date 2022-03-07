# The binomial types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.binomial-types where

open import elementary-number-theory.binomial-coefficients using (_choose-ℕ_)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.booleans using (bool; true; false)
open import foundation.connected-components-universes using
  ( component-UU-Level; type-component-UU-Level; mere-equiv-component-UU-Level;
    is-contr-component-UU-Level-empty)
open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; equiv-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr; ind-coprod)
open import foundation.decidable-embeddings using
  ( _↪d_; map-decidable-emb; is-emb-map-decidable-emb; is-decidable-emb;
    equiv-Fib-decidable-Prop; equiv-precomp-decidable-emb-equiv;
    is-prop-is-decidable-emb; is-decidable-emb-ex-falso)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop; equiv-bool-decidable-Prop;
    compute-equiv-bool-decidable-Prop; split-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; ind-Σ)
open import foundation.embeddings using (is-emb)
open import foundation.empty-types using
  ( empty; raise-empty; equiv-raise-empty; ex-falso; is-empty; empty-Prop;
    is-empty-raise-empty; raise-empty-Prop; equiv-is-empty)
open import foundation.equivalences using
  ( _≃_; equiv-postcomp-equiv; inv-equiv; _∘e_; map-equiv; id-equiv;
    equiv-precomp; is-equiv-map-equiv; equiv-precomp-equiv)
open import foundation.equivalences-maybe using (equiv-equiv-Maybe)
open import foundation.fibers-of-maps using (equiv-total-fib; fib; fib-comp)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-function-types using (equiv-postcomp)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-Σ; equiv-tot)
open import foundation.functoriality-propositional-truncation using
  ( equiv-trunc-Prop; functor-trunc-Prop)
open import foundation.logical-equivalences using (equiv-iff)
open import foundation.maybe using (Maybe)
open import foundation.mere-equivalences using
  ( mere-equiv; mere-equiv-Prop)
open import foundation.negation using (¬)
open import foundation.propositional-extensionality using
  ( is-contr-total-true-Prop; is-contr-total-false-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  ( is-proof-irrelevant-is-prop; UU-Prop; type-Prop)
open import foundation.raising-universe-levels using (map-inv-raise)
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation.type-arithmetic-coproduct-types using
  ( left-distributive-Σ-coprod; right-distributive-Σ-coprod)
open import foundation.type-arithmetic-dependent-pair-types using
  ( inv-assoc-Σ; assoc-Σ; left-unit-law-Σ-is-contr; right-unit-law-Σ-is-contr)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod-is-empty)
open import foundation.type-arithmetic-unit-type using (left-unit-law-Σ)
open import foundation.unit-type using
  ( is-contr-raise-unit; is-contr-unit; raise-unit-Prop; raise-star; unit; star)
open import foundation.universal-property-empty-type using
  ( universal-property-empty')
open import foundation.universal-property-maybe using
  ( equiv-universal-property-Maybe)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import univalent-combinatorics.equivalences-standard-finite-types using
  ( Fin-add-ℕ)
open import univalent-combinatorics.finite-types using
  ( Fin-UU-Fin-Level; has-cardinality; has-cardinality-Prop; UU-Fin-Level;
    type-UU-Fin-Level; mere-equiv-UU-Fin-Level; UU-Fin; type-UU-Fin;
    mere-equiv-UU-Fin; has-finite-cardinality; is-finite;
    is-finite-has-finite-cardinality; has-finite-cardinality-is-finite; 𝔽;
    type-𝔽; is-finite-type-𝔽; is-finite-equiv)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-contr-Fin-one-ℕ)
```

## Idea

The binomial types are a categorification of the binomial coefficients. The binomial type `(A choose B)` is the type of decidable embeddings from types merely equal to `B` into `A`.

## Definitions

```agda
binomial-type-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪d X)

type-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → binomial-type-Level l3 X Y → UU l3
type-binomial-type-Level Z = type-component-UU-Level (pr1 Z)

abstract
  mere-compute-binomial-type-Level :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
    (Z : binomial-type-Level l3 X Y) →
    mere-equiv Y (type-binomial-type-Level Z)
  mere-compute-binomial-type-Level Z = mere-equiv-component-UU-Level (pr1 Z)

decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z ↪d X
decidable-emb-binomial-type-Level Z = pr2 Z

map-decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z → X
map-decidable-emb-binomial-type-Level Z =
  map-decidable-emb (decidable-emb-binomial-type-Level Z)

abstract
  is-emb-map-emb-binomial-type-Level :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
    (Z : binomial-type-Level l3 X Y) →
    is-emb (map-decidable-emb-binomial-type-Level Z)
  is-emb-map-emb-binomial-type-Level Z =
    is-emb-map-decidable-emb (decidable-emb-binomial-type-Level Z)

-- We now define the standard binomial types

binomial-type : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type {l1} {l2} X Y = binomial-type-Level (l1 ⊔ l2) X Y

type-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → binomial-type X Y → UU (l1 ⊔ l2)
type-binomial-type Z = type-component-UU-Level (pr1 Z)

abstract
  mere-compute-binomial-type :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
    mere-equiv Y (type-binomial-type Z)
  mere-compute-binomial-type Z = mere-equiv-component-UU-Level (pr1 Z)

decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z ↪d X
decidable-emb-binomial-type Z = pr2 Z

map-decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z → X
map-decidable-emb-binomial-type Z =
  map-decidable-emb (decidable-emb-binomial-type Z)

abstract
  is-emb-map-emb-binomial-type :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
    is-emb (map-decidable-emb-binomial-type Z)
  is-emb-map-emb-binomial-type Z =
    is-emb-map-decidable-emb (decidable-emb-binomial-type Z)

-- Proposition 17.5.6

binomial-type-Level' :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level' l A B =
  Σ ( A → decidable-Prop l)
    ( λ P → mere-equiv B (Σ A (λ x → type-decidable-Prop (P x))))

compute-binomial-type-Level :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type-Level (l1 ⊔ l) A B ≃ binomial-type-Level' (l1 ⊔ l) A B
compute-binomial-type-Level l {l1} {l2} A B =
  ( ( ( equiv-Σ
        ( λ P → mere-equiv B (Σ A (λ x → type-decidable-Prop (P x))))
        ( equiv-Fib-decidable-Prop l A)
        ( λ e →
          equiv-trunc-Prop
            ( equiv-postcomp-equiv
              ( inv-equiv (equiv-total-fib (pr1 (pr2 e)))) B))) ∘e
      ( inv-assoc-Σ
        ( UU (l1 ⊔ l))
        ( λ X → X ↪d A)
        ( λ X → mere-equiv B (pr1 X)))) ∘e
    ( equiv-tot (λ X → commutative-prod))) ∘e
  ( assoc-Σ (UU (l1 ⊔ l)) (λ X → mere-equiv B X) (λ X → (pr1 X) ↪d A))

binomial-type' :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type' {l1} {l2} A B = binomial-type-Level' (l1 ⊔ l2) A B

compute-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ binomial-type' A B
compute-binomial-type {l1} {l2} A B =
  compute-binomial-type-Level (l1 ⊔ l2) A B

-- Remark 17.5.7

-- Note that the universe level of small-binomial-type is lower

small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
small-binomial-type A B =
  Σ (A → bool) (λ f → mere-equiv B (fib f true))

compute-small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ small-binomial-type A B
compute-small-binomial-type A B =
  ( equiv-Σ
    ( λ f → mere-equiv B (fib f true))
    ( equiv-postcomp A equiv-bool-decidable-Prop)
    ( λ P →
      equiv-trunc-Prop
        ( equiv-postcomp-equiv
          ( equiv-tot (λ a → compute-equiv-bool-decidable-Prop (P a)))
          ( B)))) ∘e
  ( compute-binomial-type A B)
```

```agda
abstract
  binomial-type-over-empty :
    {l : Level} {X : UU l} → is-contr (binomial-type X empty)
  binomial-type-over-empty {l} {X} =
    is-contr-equiv
      ( raise-empty l ↪d X)
      ( left-unit-law-Σ-is-contr
        ( is-contr-component-UU-Level-empty l)
        ( Fin-UU-Fin-Level l zero-ℕ))
      ( is-contr-equiv
        ( empty ↪d X)
        ( equiv-precomp-decidable-emb-equiv (equiv-raise-empty l) X)
        ( is-contr-equiv
          ( is-decidable-emb ex-falso)
          ( left-unit-law-Σ-is-contr (universal-property-empty' X) ex-falso)
          ( is-proof-irrelevant-is-prop
            ( is-prop-is-decidable-emb ex-falso)
            ( is-decidable-emb-ex-falso))))

abstract
  binomial-type-empty-under :
    {l : Level} {X : UU l} →
    type-trunc-Prop X → is-empty (binomial-type empty X)
  binomial-type-empty-under H Y =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ x →
        apply-universal-property-trunc-Prop (pr2 (pr1 Y)) empty-Prop
          ( λ e → map-decidable-emb (pr2 Y) (map-equiv e x)))

abstract
  recursion-binomial-type' :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type' (Maybe A) (Maybe B) ≃
    coprod (binomial-type' A B) (binomial-type' A (Maybe B))
  recursion-binomial-type' A B =
    ( ( ( left-distributive-Σ-coprod
          ( A → decidable-Prop _)
          ( λ P → mere-equiv B (Σ A _))
          ( λ P → mere-equiv (Maybe B) (Σ A _))) ∘e
        ( equiv-tot
          ( λ P →
            ( ( equiv-coprod
                ( ( ( equiv-iff
                      ( mere-equiv-Prop (Maybe B) (Maybe (Σ A _)))
                      ( mere-equiv-Prop B (Σ A _))
                      ( functor-trunc-Prop (equiv-equiv-Maybe))
                      ( functor-trunc-Prop
                        ( λ e → equiv-coprod e id-equiv))) ∘e
                    ( equiv-trunc-Prop
                      ( equiv-postcomp-equiv
                        ( equiv-coprod
                          ( id-equiv)
                          ( equiv-is-contr is-contr-raise-unit is-contr-unit))
                        ( Maybe B)))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-contr-total-true-Prop)
                    ( pair (raise-unit-Prop _) raise-star)))
                ( ( equiv-trunc-Prop
                    ( equiv-postcomp-equiv
                      ( right-unit-law-coprod-is-empty
                        ( Σ A _)
                        ( raise-empty _)
                        ( is-empty-raise-empty))
                      ( Maybe B))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-contr-total-false-Prop)
                    ( pair (raise-empty-Prop _) map-inv-raise)))) ∘e
              ( right-distributive-Σ-coprod
                ( Σ (UU-Prop _) type-Prop)
                ( Σ (UU-Prop _) (¬ ∘ type-Prop))
                ( ind-coprod _
                  ( λ Q →
                    mere-equiv (Maybe B) (coprod (Σ A _) (type-Prop (pr1 Q))))
                  ( λ Q →
                    mere-equiv
                      ( Maybe B)
                      ( coprod (Σ A _) (type-Prop (pr1 Q))))))) ∘e
            ( equiv-Σ
              ( ind-coprod _
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( coprod
                      ( Σ A (λ a → type-decidable-Prop (P a)))
                      ( type-Prop (pr1 Q))))
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( coprod
                      ( Σ A (λ a → type-decidable-Prop (P a)))
                      ( type-Prop (pr1 Q)))))
              ( split-decidable-Prop)
              ( ind-Σ
                ( λ Q →
                  ind-Σ
                    ( λ H →
                      ind-coprod _ ( λ q → id-equiv) (λ q → id-equiv)))))))) ∘e
      ( assoc-Σ
        ( A → decidable-Prop _)
        ( λ a → decidable-Prop _)
        ( λ t →
          mere-equiv
            ( Maybe B)
            ( coprod
              ( Σ A (λ a → type-decidable-Prop (pr1 t a)))
              ( type-decidable-Prop (pr2 t)))))) ∘e
    ( equiv-Σ
      ( λ p →
        mere-equiv
          ( Maybe B)
          ( coprod
            ( Σ A (λ a → type-decidable-Prop (pr1 p a)))
            ( type-decidable-Prop (pr2 p))))
      ( equiv-universal-property-Maybe)
      ( λ u →
        equiv-trunc-Prop
          ( equiv-postcomp-equiv
            ( ( equiv-coprod
                ( id-equiv)
                ( left-unit-law-Σ (λ y → type-decidable-Prop (u (inr y))))) ∘e
              ( right-distributive-Σ-coprod A unit
                ( λ x → type-decidable-Prop (u x))))
            ( Maybe B))))

abstract
  binomial-type-Maybe :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type (Maybe A) (Maybe B) ≃
    coprod (binomial-type A B) (binomial-type A (Maybe B))
  binomial-type-Maybe A B =
    ( inv-equiv
      ( equiv-coprod
        ( compute-binomial-type A B)
        ( compute-binomial-type A (Maybe B))) ∘e
      ( recursion-binomial-type' A B)) ∘e
    ( compute-binomial-type (Maybe A) (Maybe B))

-- Theorem 17.5.9

equiv-small-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → small-binomial-type A' B' ≃ small-binomial-type A B
equiv-small-binomial-type {l1} {l2} {l3} {l4} {A} {A'} {B} {B'} e f =
  equiv-Σ
    ( λ P → mere-equiv B (fib P true))
    ( equiv-precomp e bool)
    ( λ P →
      equiv-trunc-Prop
        ( ( equiv-postcomp-equiv
            ( inv-equiv
              ( ( right-unit-law-Σ-is-contr
                  ( λ u →
                    is-contr-map-is-equiv (is-equiv-map-equiv e) (pr1 u))) ∘e
                ( fib-comp P (map-equiv e) true))) B) ∘e
          ( equiv-precomp-equiv f (fib P true))))

equiv-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → binomial-type A' B' ≃ binomial-type A B
equiv-binomial-type e f =
  ( ( inv-equiv (compute-small-binomial-type _ _)) ∘e
    ( equiv-small-binomial-type e f)) ∘e
  ( compute-small-binomial-type _ _)

binomial-type-Fin :
  (n m : ℕ) → binomial-type (Fin n) (Fin m) ≃ Fin (n choose-ℕ m)
binomial-type-Fin zero-ℕ zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-one-ℕ
binomial-type-Fin zero-ℕ (succ-ℕ m) =
  equiv-is-empty (binomial-type-empty-under (unit-trunc-Prop (inr star))) id
binomial-type-Fin (succ-ℕ n) zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-one-ℕ
binomial-type-Fin (succ-ℕ n) (succ-ℕ m) =
  ( ( inv-equiv (Fin-add-ℕ (n choose-ℕ m) (n choose-ℕ succ-ℕ m))) ∘e
    ( equiv-coprod
      ( binomial-type-Fin n m)
      ( binomial-type-Fin n (succ-ℕ m)))) ∘e
  ( binomial-type-Maybe (Fin n) (Fin m))

has-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {n m : ℕ} →
  has-cardinality n A → has-cardinality m B →
  has-cardinality (n choose-ℕ m) (binomial-type A B)
has-cardinality-binomial-type {A = A} {B} {n} {m} H K =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-Prop (n choose-ℕ m) (binomial-type A B))
    ( λ e →
      apply-universal-property-trunc-Prop K
        ( has-cardinality-Prop (n choose-ℕ m) (binomial-type A B))
        ( λ f →
          unit-trunc-Prop
            ( inv-equiv
              ( binomial-type-Fin n m ∘e equiv-binomial-type e f))))

binomial-type-UU-Fin-Level :
  {l1 l2 : Level} {n m : ℕ} → UU-Fin-Level l1 n → UU-Fin-Level l2 m →
  UU-Fin-Level (lsuc l1 ⊔ lsuc l2) (n choose-ℕ m)
pr1 (binomial-type-UU-Fin-Level A B) =
  binomial-type (type-UU-Fin-Level A) (type-UU-Fin-Level B)
pr2 (binomial-type-UU-Fin-Level A B) =
  has-cardinality-binomial-type
    ( mere-equiv-UU-Fin-Level A)
    ( mere-equiv-UU-Fin-Level B)

binomial-type-UU-Fin :
  {n m : ℕ} → UU-Fin n → UU-Fin m → UU-Fin (n choose-ℕ m)
pr1 (binomial-type-UU-Fin {n} {m} A B) =
  small-binomial-type (type-UU-Fin A) (type-UU-Fin B)
pr2 (binomial-type-UU-Fin {n} {m} A B) =
  apply-universal-property-trunc-Prop
    ( has-cardinality-binomial-type
      ( mere-equiv-UU-Fin A)
      ( mere-equiv-UU-Fin B))
    ( mere-equiv-Prop
      ( Fin (n choose-ℕ m))
      ( small-binomial-type (pr1 A) (pr1 B)))
    ( λ e →
      unit-trunc-Prop
        ( ( compute-small-binomial-type (type-UU-Fin A) (type-UU-Fin B)) ∘e
          ( e)))

has-finite-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-finite-cardinality A → has-finite-cardinality B →
  has-finite-cardinality (binomial-type A B)
pr1 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) = n choose-ℕ m
pr2 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) =
  has-cardinality-binomial-type H K

abstract
  is-finite-binomial-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (binomial-type A B)
  is-finite-binomial-type H K =
    is-finite-has-finite-cardinality
      ( has-finite-cardinality-binomial-type
        ( has-finite-cardinality-is-finite H)
        ( has-finite-cardinality-is-finite K))

binomial-type-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (binomial-type-𝔽 A B) = small-binomial-type (type-𝔽 A) (type-𝔽 B)
pr2 (binomial-type-𝔽 A B) =
  is-finite-equiv
    ( compute-small-binomial-type (type-𝔽 A) (type-𝔽 B))
    ( is-finite-binomial-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B))
```
