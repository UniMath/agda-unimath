# Disjunctions

```agda
module univalent-combinatorics.disjunction where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universal-quantification
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

### Given a function `(i : Fin n) → (A i) ∨ (B i)`, we have `(∀' (Fin n) A) ∨ (∃ (Fin n) B)`

```agda
Π-disjunction-Fin :
  {l1 l2 : Level} → (n : ℕ) (A : Fin n → Prop l1) (B : Fin n → Prop l2) →
  ((i : Fin n) → type-disjunction-Prop (A i) (B i)) →
  type-disjunction-Prop (Π-Prop (Fin n) A) (∃ (Fin n) B)
Π-disjunction-Fin zero-ℕ _ _ _ = inl-disjunction (λ ())
Π-disjunction-Fin (succ-ℕ n) A B f =
  let motive = Π-Prop (Fin (succ-ℕ n)) A ∨ (∃ (Fin (succ-ℕ n)) B)
  in
    elim-disjunction
      ( motive)
      ( λ Πi<n:A →
        elim-disjunction
          ( motive)
          ( λ An →
            inl-disjunction
              ( λ where
                (inl i) → Πi<n:A i
                (inr _) → An))
          ( inr-disjunction ∘ intro-exists (neg-one-Fin n))
          ( f (neg-one-Fin n)))
      ( inr-disjunction ∘ map-exists (type-Prop ∘ B) inl (λ _ Bi → Bi))
      ( Π-disjunction-Fin n (A ∘ inl) (B ∘ inl) (f ∘ inl))
```

### Given a finitely enumerable type `X` and a function `(x : X) → (A x) ∨ (B x)`, we have `(∀' X A) ∨ (∃ X B)`

```agda
Π-disjunction-finite-enumeration :
  {l1 l2 l3 : Level} {X : UU l1} (e : finite-enumeration X)
  (A : X → Prop l2) (B : X → Prop l3) →
  ((x : X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop (∀' X A) (∃ X B)
Π-disjunction-finite-enumeration {X = X} (n , Fin-n↠X) A B f =
  elim-disjunction
    ( (∀' X A) ∨ (∃ X B))
    ( λ ∀iA →
      inl-disjunction
        ( λ x →
          rec-trunc-Prop
            ( A x)
            ( λ (i , Fi=x) → tr (type-Prop ∘ A) Fi=x (∀iA i))
            ( is-surjective-map-surjection Fin-n↠X x)))
    ( inr-disjunction ∘
      map-exists (type-Prop ∘ B) (map-surjection Fin-n↠X) (λ _ → id))
    ( Π-disjunction-Fin
      ( n)
      ( A ∘ map-surjection Fin-n↠X)
      ( B ∘ map-surjection Fin-n↠X)
      ( f ∘ map-surjection Fin-n↠X))

Π-disjunction-Finitely-Enumerable-Type :
  {l1 l2 l3 : Level} (X : Finitely-Enumerable-Type l1)
  (A : type-Finitely-Enumerable-Type X → Prop l2)
  (B : type-Finitely-Enumerable-Type X → Prop l3) →
  ((x : type-Finitely-Enumerable-Type X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop
    (∀' (type-Finitely-Enumerable-Type X) A)
    (∃ (type-Finitely-Enumerable-Type X) B)
Π-disjunction-Finitely-Enumerable-Type (X , ∃eX) A B f =
  rec-trunc-Prop
    ( ∀' X A ∨ ∃ X B)
    ( λ eX → Π-disjunction-finite-enumeration eX A B f)
    ( ∃eX)
```

### Given a finite type `X` and a function `(x : X) → (A x) ∨ (B x)`, we have `(∀' X A) ∨ (∃ X B)`

```agda
Π-disjunction-Finite-Type :
  {l1 l2 l3 : Level} (X : Finite-Type l1)
  (A : type-Finite-Type X → Prop l2) (B : type-Finite-Type X → Prop l3) →
  ((x : type-Finite-Type X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop (∀' (type-Finite-Type X) A) (∃ (type-Finite-Type X) B)
Π-disjunction-Finite-Type X =
  Π-disjunction-Finitely-Enumerable-Type
    ( finitely-enumerable-type-Finite-Type X)
```
