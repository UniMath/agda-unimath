# Exclusive disjunction of propositions

```agda
module foundation.exclusive-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.symmetric-operations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The exclusive disjunction of two propositions `P` and `Q` is the proposition
that `P` holds and `Q` doesn't hold or `P` doesn't hold and `Q` holds.

## Definitions

### Exclusive disjunction of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor : UU (l1 ⊔ l2)
  xor = (A × ¬ B) + (B × ¬ A)
```

### Exclusive disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop : Prop (l1 ⊔ l2)
  xor-Prop =
    coprod-Prop
      ( conj-Prop P (neg-Prop Q))
      ( conj-Prop Q (neg-Prop P))
      ( λ p q → pr2 q (pr1 p))

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = type-Prop xor-Prop

  abstract
    is-prop-type-xor-Prop : is-prop type-xor-Prop
    is-prop-type-xor-Prop = is-prop-type-Prop xor-Prop
```

### The symmetric operation of exclusive disjunction

```agda
predicate-symmetric-xor :
  {l : Level} (p : unordered-pair (UU l)) → type-unordered-pair p → UU l
predicate-symmetric-xor p x =
  ( element-unordered-pair p x) × (¬ (other-element-unordered-pair p x))

symmetric-xor : {l : Level} → symmetric-operation (UU l) (UU l)
symmetric-xor p = Σ (type-unordered-pair p) (predicate-symmetric-xor p)
```

### The symmetric operation of exclusive disjunction of propositions

```agda
predicate-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  type-unordered-pair p → UU l
predicate-symmetric-xor-Prop p =
  predicate-symmetric-xor (map-unordered-pair type-Prop p)

type-symmetric-xor-Prop :
  {l : Level} → symmetric-operation (Prop l) (UU l)
type-symmetric-xor-Prop p = symmetric-xor (map-unordered-pair type-Prop p)

all-elements-equal-type-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  all-elements-equal (type-symmetric-xor-Prop p)
all-elements-equal-type-symmetric-xor-Prop (pair X P) x y =
  cases-is-prop-type-symmetric-xor-Prop
    ( has-decidable-equality-is-finite
      ( is-finite-type-UU-Fin 2 X)
      ( pr1 x)
      ( pr1 y))
  where
  cases-is-prop-type-symmetric-xor-Prop :
    is-decidable (pr1 x ＝ pr1 y) → x ＝ y
  cases-is-prop-type-symmetric-xor-Prop (inl p) =
    eq-pair-Σ
      ( p)
      ( eq-is-prop (is-prop-prod (is-prop-type-Prop (P (pr1 y))) is-prop-neg))
  cases-is-prop-type-symmetric-xor-Prop (inr np) =
    ex-falso
      ( tr
        ( λ z → ¬ (type-Prop (P z)))
        ( compute-swap-2-Element-Type X (pr1 x) (pr1 y) np)
        ( pr2 (pr2 x))
        ( pr1 (pr2 y)))

is-prop-type-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  is-prop (type-symmetric-xor-Prop p)
is-prop-type-symmetric-xor-Prop p =
  is-prop-all-elements-equal
    ( all-elements-equal-type-symmetric-xor-Prop p)

symmetric-xor-Prop :
  {l : Level} → symmetric-operation (Prop l) (Prop l)
pr1 (symmetric-xor-Prop E) = type-symmetric-xor-Prop E
pr2 (symmetric-xor-Prop E) = is-prop-type-symmetric-xor-Prop E
```

### Second definition of exclusiove disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop' : Prop (l1 ⊔ l2)
  xor-Prop' = is-contr-Prop (type-Prop P + type-Prop Q)

  type-xor-Prop' : UU (l1 ⊔ l2)
  type-xor-Prop' = type-Prop xor-Prop'
```

## Properties

### The definitions `xor-Prop` and `xor-Prop'` are equivalent

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-equiv-xor-Prop : type-xor-Prop' P Q → type-xor-Prop P Q
  map-equiv-xor-Prop (pair (inl p) H) =
    inl (pair p (λ q → is-empty-eq-coprod-inl-inr p q (H (inr q))))
  map-equiv-xor-Prop (pair (inr q) H) =
    inr (pair q (λ p → is-empty-eq-coprod-inr-inl q p (H (inl p))))

  equiv-xor-Prop : type-xor-Prop' P Q ≃ type-xor-Prop P Q
  equiv-xor-Prop =
    ( equiv-coprod
      ( equiv-tot
        ( λ p →
          ( ( equiv-map-Π
              ( λ q → compute-eq-coprod-inl-inr p q)) ∘e
            ( left-unit-law-prod-is-contr
              ( is-contr-Π
                ( λ p' →
                  is-contr-equiv'
                    ( p ＝ p')
                    ( equiv-ap-emb (emb-inl (type-Prop P) (type-Prop Q)))
                    ( is-prop-type-Prop P p p'))))) ∘e
          ( equiv-dependent-universal-property-coprod (λ x → inl p ＝ x))))
      ( equiv-tot
        ( λ q →
          ( ( equiv-map-Π
              ( λ p → compute-eq-coprod-inr-inl q p)) ∘e
            ( right-unit-law-prod-is-contr
              ( is-contr-Π
                ( λ q' →
                  is-contr-equiv'
                    ( q ＝ q')
                    ( equiv-ap-emb (emb-inr (type-Prop P) (type-Prop Q)))
                    ( is-prop-type-Prop Q q q'))))) ∘e
          ( equiv-dependent-universal-property-coprod (λ x → inr q ＝ x))))) ∘e
    ( right-distributive-Σ-coprod
      ( type-Prop P)
      ( type-Prop Q)
      ( λ x → (y : type-Prop P + type-Prop Q) → x ＝ y))
```

### The symmetric exclusive disjunction at a standard unordered pair

```agda
module _
  {l : Level} {A B : UU l}
  where

  xor-symmetric-xor :
    symmetric-xor (standard-unordered-pair A B) → xor A B
  xor-symmetric-xor (pair (inl (inr star)) (pair p nq)) =
    inl
      ( pair p
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-two-ℕ (zero-Fin 1))
          ( nq)))
  xor-symmetric-xor (pair (inr star) (pair q np)) =
    inr
      ( pair
        ( q)
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-two-ℕ (one-Fin 1))
          ( np)))

  symmetric-xor-xor :
    xor A B → symmetric-xor (standard-unordered-pair A B)
  pr1 (symmetric-xor-xor (inl (pair a nb))) = (zero-Fin 1)
  pr1 (pr2 (symmetric-xor-xor (inl (pair a nb)))) = a
  pr2 (pr2 (symmetric-xor-xor (inl (pair a nb)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-two-ℕ (zero-Fin 1)))
      ( nb)
  pr1 (symmetric-xor-xor (inr (pair na b))) = (one-Fin 1)
  pr1 (pr2 (symmetric-xor-xor (inr (pair b na)))) = b
  pr2 (pr2 (symmetric-xor-xor (inr (pair b na)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-two-ℕ (one-Fin 1)))
      ( na)

{-
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
                      ( inv (compute-swap-Fin-two-ℕ (zero-Fin ?)))
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
              ( inv (compute-swap-Fin-two-ℕ (one-Fin ?)))
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
-}
```

```agda
module _
  {l : Level} (P Q : Prop l)
  where

  xor-symmetric-xor-Prop :
    type-hom-Prop
      ( symmetric-xor-Prop (standard-unordered-pair P Q))
      ( xor-Prop P Q)
  xor-symmetric-xor-Prop (pair (inl (inr star)) (pair p nq)) =
    inl
      ( pair p
        ( tr
          ( λ t →
            ¬ ( type-Prop
                ( element-unordered-pair (standard-unordered-pair P Q) t)))
          ( compute-swap-Fin-two-ℕ (zero-Fin 1))
          ( nq)))
  xor-symmetric-xor-Prop (pair (inr star) (pair q np)) =
    inr
      ( pair q
        ( tr
          ( λ t →
            ¬ ( type-Prop
                ( element-unordered-pair (standard-unordered-pair P Q) t)))
          ( compute-swap-Fin-two-ℕ (one-Fin 1))
          ( np)))

  symmetric-xor-xor-Prop :
    type-hom-Prop
      ( xor-Prop P Q)
      ( symmetric-xor-Prop (standard-unordered-pair P Q))
  pr1 (symmetric-xor-xor-Prop (inl (pair p nq))) = (zero-Fin 1)
  pr1 (pr2 (symmetric-xor-xor-Prop (inl (pair p nq)))) = p
  pr2 (pr2 (symmetric-xor-xor-Prop (inl (pair p nq)))) =
    tr
      ( λ t →
        ¬ (type-Prop (element-unordered-pair (standard-unordered-pair P Q) t)))
      ( inv (compute-swap-Fin-two-ℕ (zero-Fin 1)))
      ( nq)
  pr1 (symmetric-xor-xor-Prop (inr (pair q np))) = (one-Fin 1)
  pr1 (pr2 (symmetric-xor-xor-Prop (inr (pair q np)))) = q
  pr2 (pr2 (symmetric-xor-xor-Prop (inr (pair q np)))) =
    tr
      ( λ t →
        ¬ (type-Prop (element-unordered-pair (standard-unordered-pair P Q) t)))
      ( inv (compute-swap-Fin-two-ℕ (one-Fin 1)))
      ( np)

eq-commmutative-xor-xor :
  {l : Level} (P Q : Prop l) →
  symmetric-xor-Prop (standard-unordered-pair P Q) ＝ xor-Prop P Q
eq-commmutative-xor-xor P Q =
  eq-iff (xor-symmetric-xor-Prop P Q) (symmetric-xor-xor-Prop P Q)
```

### Exclusive disjunction of decidable propositions

```agda
is-decidable-xor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (xor A B)
is-decidable-xor d e =
  is-decidable-coprod
    ( is-decidable-prod d (is-decidable-neg e))
    ( is-decidable-prod e (is-decidable-neg d))

xor-Decidable-Prop :
  {l1 l2 : Level} → Decidable-Prop l1 → Decidable-Prop l2 →
  Decidable-Prop (l1 ⊔ l2)
pr1 (xor-Decidable-Prop P Q) =
  type-xor-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr1 (pr2 (xor-Decidable-Prop P Q)) =
  is-prop-type-xor-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr2 (pr2 (xor-Decidable-Prop P Q)) =
  is-decidable-coprod
    ( is-decidable-prod
      ( is-decidable-Decidable-Prop P)
      ( is-decidable-neg (is-decidable-Decidable-Prop Q)))
    ( is-decidable-prod
      ( is-decidable-Decidable-Prop Q)
      ( is-decidable-neg (is-decidable-Decidable-Prop P)))
```
