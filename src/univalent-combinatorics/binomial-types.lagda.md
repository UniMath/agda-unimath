# The binomial types

```agda
module univalent-combinatorics.binomial-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.connected-components-universes
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.functoriality-propositional-truncation
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "binomial types" Agda=binomial-type}} are a categorification of
the [binomial coefficients](elementary-number-theory.binomial-coefficients.md).
The binomial type `(A choose B)` is the type of
[decidable embeddings](foundation.decidable-embeddings.md) from types
[merely equivalent](foundation.mere-equivalences.md) to `B` into `A`.

## Definitions

### Binomial types of a given universe level

```agda
binomial-type-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪ᵈ X)

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y)
  where

  type-binomial-type-Level : UU l3
  type-binomial-type-Level = type-component-UU-Level (pr1 Z)

  abstract
    mere-compute-binomial-type-Level :
      mere-equiv Y type-binomial-type-Level
    mere-compute-binomial-type-Level = mere-equiv-component-UU-Level (pr1 Z)

  decidable-emb-binomial-type-Level : type-binomial-type-Level ↪ᵈ X
  decidable-emb-binomial-type-Level = pr2 Z

  map-decidable-emb-binomial-type-Level : type-binomial-type-Level → X
  map-decidable-emb-binomial-type-Level =
    map-decidable-emb decidable-emb-binomial-type-Level

  abstract
    is-emb-map-emb-binomial-type-Level :
      is-emb map-decidable-emb-binomial-type-Level
    is-emb-map-emb-binomial-type-Level =
      is-emb-map-decidable-emb decidable-emb-binomial-type-Level
```

### The standard binomial types

```agda
binomial-type : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type {l1} {l2} X Y = binomial-type-Level (l1 ⊔ l2) X Y

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y)
  where

  type-binomial-type : UU (l1 ⊔ l2)
  type-binomial-type = type-component-UU-Level (pr1 Z)

  abstract
    mere-compute-binomial-type : mere-equiv Y type-binomial-type
    mere-compute-binomial-type = mere-equiv-component-UU-Level (pr1 Z)

  decidable-emb-binomial-type : type-binomial-type ↪ᵈ X
  decidable-emb-binomial-type = pr2 Z

  map-decidable-emb-binomial-type : type-binomial-type → X
  map-decidable-emb-binomial-type =
    map-decidable-emb decidable-emb-binomial-type

  abstract
    is-emb-map-emb-binomial-type : is-emb map-decidable-emb-binomial-type
    is-emb-map-emb-binomial-type =
      is-emb-map-decidable-emb decidable-emb-binomial-type
```

### The type of decidable subtypes of `A` such that the total space is merely equivalent to a given finite type

```agda
binomial-type-Level' :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level' l A B =
  Σ ( A → Decidable-Prop l)
    ( λ P → mere-equiv B (Σ A (type-Decidable-Prop ∘ P)))

binomial-type' :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type' {l1} {l2} A B = binomial-type-Level' (l1 ⊔ l2) A B
```

### The small binomial types

Note that the universe level of `small-binomial-type` is lower that the universe
level of `binomial-type`.

```agda
small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
small-binomial-type A B =
  Σ (A → bool) (λ f → mere-equiv B (fiber f true))
```

## Properties

### The binomial type `(A B)` is equivalent to the type of decidable subtypes of `A` such that the total space is merely equivalent to `B`

```agda
compute-binomial-type-Level :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type-Level (l1 ⊔ l) A B ≃ binomial-type-Level' (l1 ⊔ l) A B
compute-binomial-type-Level l {l1} {l2} A B =
  ( ( ( equiv-Σ
        ( λ P → mere-equiv B (Σ A (type-Decidable-Prop ∘ P)))
        ( equiv-Fiber-Decidable-Prop l A)
        ( λ e →
          equiv-trunc-Prop
            ( equiv-postcomp-equiv
              ( inv-equiv (equiv-total-fiber (pr1 (pr2 e)))) B))) ∘e
      ( inv-associative-Σ)) ∘e
    ( equiv-tot (λ X → commutative-product))) ∘e
  ( associative-Σ)

compute-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ binomial-type' A B
compute-binomial-type {l1} {l2} A B =
  compute-binomial-type-Level (l1 ⊔ l2) A B
```

### The bionmial type `(A B)` is equivalent to the small binomial type at `A` and `B`

```agda
compute-small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ small-binomial-type A B
compute-small-binomial-type A B =
  ( equiv-Σ
    ( λ f → mere-equiv B (fiber f true))
    ( equiv-postcomp A equiv-bool-Decidable-Prop)
    ( λ P →
      equiv-trunc-Prop
        ( equiv-postcomp-equiv
          ( equiv-tot (λ a → compute-equiv-bool-Decidable-Prop (P a)))
          ( B)))) ∘e
  ( compute-binomial-type A B)
```

### The binomial type `(A ∅)` is contractible

```agda
abstract
  binomial-type-over-empty :
    {l : Level} {X : UU l} → is-contr (binomial-type X empty)
  binomial-type-over-empty {l} {X} =
    is-contr-equiv
      ( raise-empty l ↪ᵈ X)
      ( left-unit-law-Σ-is-contr
        ( is-contr-component-UU-Level-empty l)
        ( raise-Fin-Type-With-Cardinality-ℕ l zero-ℕ))
      ( is-contr-equiv
        ( empty ↪ᵈ X)
        ( equiv-precomp-decidable-emb-equiv (compute-raise-empty l) X)
        ( is-contr-equiv
          ( is-decidable-emb ex-falso)
          ( left-unit-law-Σ-is-contr (universal-property-empty' X) ex-falso)
          ( is-proof-irrelevant-is-prop
            ( is-prop-is-decidable-emb ex-falso)
            ( is-decidable-emb-ex-falso))))
```

### The binomial type `(∅ A)` is empty

```agda
abstract
  binomial-type-empty-under :
    {l : Level} {X : UU l} →
    type-trunc-Prop X → is-empty (binomial-type empty X)
  binomial-type-empty-under H Y =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ x →
        apply-universal-property-trunc-Prop (pr2 (pr1 Y)) empty-Prop
          ( λ e → map-decidable-emb (pr2 Y) (map-equiv e x)))
```

### A recursive law for the binomial types

```agda
abstract
  recursion-binomial-type' :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type' (Maybe A) (Maybe B) ≃
    (binomial-type' A B + binomial-type' A (Maybe B))
  recursion-binomial-type' A B =
    ( ( ( left-distributive-Σ-coproduct
          ( A → Decidable-Prop _)
          ( λ P → mere-equiv B (Σ A _))
          ( λ P → mere-equiv (Maybe B) (Σ A _))) ∘e
        ( equiv-tot
          ( λ P →
            ( ( equiv-coproduct
                ( ( ( equiv-iff
                      ( mere-equiv-Prop (Maybe B) (Maybe (Σ A _)))
                      ( mere-equiv-Prop B (Σ A _))
                      ( map-trunc-Prop (equiv-equiv-Maybe))
                      ( map-trunc-Prop
                        ( λ e → equiv-coproduct e id-equiv))) ∘e
                    ( equiv-trunc-Prop
                      ( equiv-postcomp-equiv
                        ( equiv-coproduct
                          ( id-equiv)
                          ( equiv-is-contr is-contr-raise-unit is-contr-unit))
                        ( Maybe B)))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-torsorial-true-Prop)
                    ( pair (raise-unit-Prop _) raise-star)))
                ( ( equiv-trunc-Prop
                    ( equiv-postcomp-equiv
                      ( right-unit-law-coproduct-is-empty
                        ( Σ A _)
                        ( raise-empty _)
                        ( is-empty-raise-empty))
                      ( Maybe B))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-torsorial-false-Prop)
                    ( pair (raise-empty-Prop _) map-inv-raise)))) ∘e
              ( right-distributive-Σ-coproduct
                ( Σ (Prop _) type-Prop)
                ( Σ (Prop _) (¬_ ∘ type-Prop))
                ( ind-coproduct _
                  ( λ Q →
                    mere-equiv (Maybe B) ((Σ A _) + (type-Prop (pr1 Q))))
                  ( λ Q →
                    mere-equiv
                      ( Maybe B)
                      ( (Σ A _) + (type-Prop (pr1 Q))))))) ∘e
            ( equiv-Σ
              ( ind-coproduct _
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( ( Σ A (λ a → type-Decidable-Prop (P a))) +
                      ( type-Prop (pr1 Q))))
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( ( Σ A (λ a → type-Decidable-Prop (P a))) +
                      ( type-Prop (pr1 Q)))))
              ( split-Decidable-Prop)
              ( ind-Σ
                ( λ Q →
                  ind-Σ
                    ( λ H →
                      ind-coproduct
                        ( _)
                        ( λ q → id-equiv)
                        ( λ q → id-equiv)))))))) ∘e
      ( associative-Σ)) ∘e
    ( equiv-Σ
      ( λ p →
        mere-equiv
          ( Maybe B)
          ( ( Σ A (λ a → type-Decidable-Prop (pr1 p a))) +
            ( type-Decidable-Prop (pr2 p))))
      ( equiv-universal-property-Maybe)
      ( λ u →
        equiv-trunc-Prop
          ( equiv-postcomp-equiv
            ( ( equiv-coproduct
                ( id-equiv)
                ( left-unit-law-Σ (λ y → type-Decidable-Prop (u (inr y))))) ∘e
              ( right-distributive-Σ-coproduct A unit
                ( λ x → type-Decidable-Prop (u x))))
            ( Maybe B))))

abstract
  binomial-type-Maybe :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type (Maybe A) (Maybe B) ≃
    (binomial-type A B + binomial-type A (Maybe B))
  binomial-type-Maybe A B =
    ( inv-equiv
      ( equiv-coproduct
        ( compute-binomial-type A B)
        ( compute-binomial-type A (Maybe B))) ∘e
      ( recursion-binomial-type' A B)) ∘e
    ( compute-binomial-type (Maybe A) (Maybe B))
```

### The small binomial types are invariant under equivalences

```agda
equiv-small-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → small-binomial-type A' B' ≃ small-binomial-type A B
equiv-small-binomial-type {l1} {l2} {l3} {l4} {A} {A'} {B} {B'} e f =
  equiv-Σ
    ( λ P → mere-equiv B (fiber P true))
    ( equiv-precomp e bool)
    ( λ P →
      equiv-trunc-Prop
        ( ( equiv-postcomp-equiv
            ( inv-equiv
              ( ( right-unit-law-Σ-is-contr
                  ( λ u →
                    is-contr-map-is-equiv (is-equiv-map-equiv e) (pr1 u))) ∘e
                ( compute-fiber-comp P (map-equiv e) true))) B) ∘e
          ( equiv-precomp-equiv f (fiber P true))))
```

### The binomial types are invariant under equivalences

```agda
equiv-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → binomial-type A' B' ≃ binomial-type A B
equiv-binomial-type e f =
  ( ( inv-equiv (compute-small-binomial-type _ _)) ∘e
    ( equiv-small-binomial-type e f)) ∘e
  ( compute-small-binomial-type _ _)
```

### Computation of the number of elements of the binomial type `((Fin n) (Fin m))`

The computation of the number of subsets of a given cardinality of a finite set
is the [58th](literature.100-theorems.md#58) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
binomial-type-Fin :
  (n m : ℕ) → binomial-type (Fin n) (Fin m) ≃ Fin (binomial-coefficient-ℕ n m)
binomial-type-Fin zero-ℕ zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-1
binomial-type-Fin zero-ℕ (succ-ℕ m) =
  equiv-is-empty (binomial-type-empty-under (unit-trunc-Prop (inr star))) id
binomial-type-Fin (succ-ℕ n) zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-1
binomial-type-Fin (succ-ℕ n) (succ-ℕ m) =
  ( ( inv-equiv
      ( inv-compute-coproduct-Fin
        ( binomial-coefficient-ℕ n m)
        ( binomial-coefficient-ℕ n (succ-ℕ m)))) ∘e
    ( equiv-coproduct
      ( binomial-type-Fin n m)
      ( binomial-type-Fin n (succ-ℕ m)))) ∘e
  ( binomial-type-Maybe (Fin n) (Fin m))

has-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (n m : ℕ) →
  has-cardinality-ℕ n A → has-cardinality-ℕ m B →
  has-cardinality-ℕ (binomial-coefficient-ℕ n m) (binomial-type A B)
has-cardinality-binomial-type {A = A} {B} n m H K =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-ℕ-Prop (binomial-coefficient-ℕ n m) (binomial-type A B))
    ( λ e →
      apply-universal-property-trunc-Prop K
        ( has-cardinality-ℕ-Prop
          ( binomial-coefficient-ℕ n m)
          ( binomial-type A B))
        ( λ f →
          unit-trunc-Prop
            ( inv-equiv
              ( binomial-type-Fin n m ∘e equiv-binomial-type e f))))

binomial-type-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (n m : ℕ) →
  Type-With-Cardinality-ℕ l1 n → Type-With-Cardinality-ℕ l2 m →
  Type-With-Cardinality-ℕ (lsuc l1 ⊔ lsuc l2) (binomial-coefficient-ℕ n m)
pr1 (binomial-type-Type-With-Cardinality-ℕ n m A B) =
  binomial-type
    ( type-Type-With-Cardinality-ℕ n A)
    ( type-Type-With-Cardinality-ℕ m B)
pr2 (binomial-type-Type-With-Cardinality-ℕ n m A B) =
  has-cardinality-binomial-type n m
    ( has-cardinality-type-Type-With-Cardinality-ℕ n A)
    ( has-cardinality-type-Type-With-Cardinality-ℕ m B)

has-finite-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-finite-cardinality A → has-finite-cardinality B →
  has-finite-cardinality (binomial-type A B)
pr1 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) =
  binomial-coefficient-ℕ n m
pr2 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) =
  has-cardinality-binomial-type n m H K

abstract
  is-finite-binomial-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (binomial-type A B)
  is-finite-binomial-type H K =
    is-finite-has-finite-cardinality
      ( has-finite-cardinality-binomial-type
        ( has-finite-cardinality-is-finite H)
        ( has-finite-cardinality-is-finite K))

binomial-type-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (binomial-type-Finite-Type A B) =
  small-binomial-type (type-Finite-Type A) (type-Finite-Type B)
pr2 (binomial-type-Finite-Type A B) =
  is-finite-equiv
    ( compute-small-binomial-type (type-Finite-Type A) (type-Finite-Type B))
    ( is-finite-binomial-type
      ( is-finite-type-Finite-Type A)
      ( is-finite-type-Finite-Type B))
```

## References

{{#bibliography}}
