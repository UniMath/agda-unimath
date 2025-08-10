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
open import foundation.equivalences
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

### Given a function `(i : Fin n) → A i ∨ B i`, we have `∀' (Fin n) A ∨ ∃ (Fin n) B`

```agda
Π-disjunction-Fin :
  {l1 l2 : Level} → (n : ℕ) (A : Fin n → Prop l1) (B : Fin n → Prop l2) →
  ((i : Fin n) → type-disjunction-Prop (A i) (B i)) →
  type-disjunction-Prop (Π-Prop (Fin n) A) (∃ (Fin n) B)
Π-disjunction-Fin zero-ℕ _ _ _ = inl-disjunction (λ ())
Π-disjunction-Fin (succ-ℕ n) A B f =
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
  where motive = Π-Prop (Fin (succ-ℕ n)) A ∨ (∃ (Fin (succ-ℕ n)) B)
```

{- ### Given a finite type `X` and a function `(x : X) → A x ∨ B x`, we have
`∀' X A ∨ ∃ X B`

```agda
Π-disjunction-Finite-Type :
  {l1 l2 l3 : Level} (X : Finite-Type l1)
  (A : type-Finite-Type X → Prop l2) (B : type-Finite-Type X → Prop l3) →
  ((x : type-Finite-Type X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop (∀' (type-Finite-Type X) A) (∃ (type-Finite-Type X) B)
Π-disjunction-Finite-Type X A B f =
  rec-trunc-Prop
    ( motive)
    ( λ (n , Fin-n≃X) →
      elim-disjunction
        ( motive)
        ( λ ∀iA →
          inl-disjunction
            ( λ x →
              tr
                ( type-Prop ∘ A)
                ( is-section-map-inv-equiv Fin-n≃X x)
                ( ∀iA (map-inv-equiv Fin-n≃X x))))
        ( inr-disjunction ∘
          map-exists (type-Prop ∘ B) (map-equiv Fin-n≃X) (λ _ Bi → Bi))
        ( Π-disjunction-Fin
          ( n)
          ( A ∘ map-equiv Fin-n≃X)
          ( B ∘ map-equiv Fin-n≃X)
          ( f ∘ map-equiv Fin-n≃X)))
    ( is-finite-type-Finite-Type X)
  where motive = ∀' (type-Finite-Type X) A ∨ ∃ (type-Finite-Type X) B
```

-}

### Given a finitely enumerable type `X` and a function `(x : X) → A x ∨ B x`, we have `∀' X A ∨ ∃ X B`

```agda
Π-disjunction-finite-enumeration :
  {l1 l2 l3 : Level} (X : UU l1) (e : finite-enumeration X)
  (A : X → Prop l2) (B : X → Prop l3) →
  ((x : X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop (∀' X A) (∃ X B)
Π-disjunction-finite-enumeration X (n , Fin-n⇸X?) A B f =
  elim-disjunction
    ( motive)
    {!   !}
    {!   !}
    ( Π-disjunction-Fin n {! A ∘ map-surjection Fin-n⇸X  !} {!   !} {!   !})
  where motive = ∀' X A ∨ ∃ X B

Π-disjunction-Finitely-Enumerable-Type :
  {l1 l2 l3 : Level} (X : Finitely-Enumerable-Type l1)
  (A : type-Finitely-Enumerable-Type X → Prop l2)
  (B : type-Finitely-Enumerable-Type X → Prop l3) →
  ((x : type-Finitely-Enumerable-Type X) → type-disjunction-Prop (A x) (B x)) →
  type-disjunction-Prop
    (∀' (type-Finitely-Enumerable-Type X) A)
    (∃ (type-Finitely-Enumerable-Type X) B)
Π-disjunction-Finitely-Enumerable-Type X A B f =
  {!   !}
```
