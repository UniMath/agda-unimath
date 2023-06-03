# The universal property of the integers

```agda
module elementary-number-theory.universal-property-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The universal property of the integers asserts that for any type `X` equipped
with a point `x : X` and an equivalence `e : X ≃ X`, the type of maps from `ℤ`
to `X`, preserving the structure of the integers (zero and the successor
equivalence), is contractible.

The dependent universal property of the integers asserts a similar statement for
sections of any type family `P` over the integers, equipped with a point
`p0 : P zero-ℤ` and a family of equivalneces `(P k) ≃ (P (succ-ℤ k))` for every
integer `k`.

## Definitions

### Integer elimination

```agda
module _
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k ≃ (P (succ-ℤ k))))
  where

  abstract
    elim-ℤ : (k : ℤ) → P k
    elim-ℤ (inl zero-ℕ) =
      map-inv-is-equiv (is-equiv-map-equiv (pS neg-one-ℤ)) p0
    elim-ℤ (inl (succ-ℕ x)) =
      map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
        ( elim-ℤ (inl x))
    elim-ℤ (inr (inl star)) = p0
    elim-ℤ (inr (inr zero-ℕ)) = map-equiv (pS zero-ℤ) p0
    elim-ℤ (inr (inr (succ-ℕ x))) =
      map-equiv
        ( pS (inr (inr x)))
        ( elim-ℤ (inr (inr x)))

    compute-zero-elim-ℤ : (elim-ℤ zero-ℤ) ＝ p0
    compute-zero-elim-ℤ = refl

    compute-succ-elim-ℤ :
      (k : ℤ) → (elim-ℤ (succ-ℤ k)) ＝ (map-equiv (pS k) (elim-ℤ k))
    compute-succ-elim-ℤ (inl zero-ℕ) =
      inv
        ( issec-map-inv-is-equiv
          ( is-equiv-map-equiv (pS (inl zero-ℕ)))
          ( elim-ℤ (succ-ℤ (inl zero-ℕ))))
    compute-succ-elim-ℤ (inl (succ-ℕ x)) =
      inv
        ( issec-map-inv-is-equiv
          ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
          ( elim-ℤ (succ-ℤ (inl (succ-ℕ x)))))
    compute-succ-elim-ℤ (inr (inl star)) = refl
    compute-succ-elim-ℤ (inr (inr x)) = refl
```

### Structure preserving dependent maps from the integers

```agda
  ELIM-ℤ : UU l1
  ELIM-ℤ =
    Σ ( ( k : ℤ) → P k)
      ( λ f →
        ( ( (f zero-ℤ) ＝ p0) ×
          ( (k : ℤ) → ((f (succ-ℤ k)) ＝ ((map-equiv (pS k)) (f k))))))

  Elim-ℤ : ELIM-ℤ
  pr1 Elim-ℤ = elim-ℤ
  pr2 Elim-ℤ = ( compute-zero-elim-ℤ , compute-succ-elim-ℤ)

  equiv-comparison-map-Eq-ELIM-ℤ :
    ( s t : ELIM-ℤ) (k : ℤ) →
    (((pr1 s) k) ＝ ((pr1 t) k)) ≃ (((pr1 s) (succ-ℤ k)) ＝ ((pr1 t) (succ-ℤ k)))
  equiv-comparison-map-Eq-ELIM-ℤ s t k =
    ( ( equiv-concat (pr2 (pr2 s) k) (pr1 t (succ-ℤ k))) ∘e
      ( equiv-concat' (map-equiv (pS k) (pr1 s k)) (inv (pr2 (pr2 t) k)))) ∘e
    ( equiv-ap (pS k) (pr1 s k) (pr1 t k))

  zero-Eq-ELIM-ℤ : (s t : ELIM-ℤ) (H : (pr1 s) ~ (pr1 t)) → UU l1
  zero-Eq-ELIM-ℤ s t H =
    (H zero-ℤ) ＝ ((pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))

  succ-Eq-ELIM-ℤ : (s t : ELIM-ℤ) (H : (pr1 s) ~ (pr1 t)) → UU l1
  succ-Eq-ELIM-ℤ s t H =
    ( k : ℤ) →
      ( H (succ-ℤ k)) ＝
      ( map-equiv (equiv-comparison-map-Eq-ELIM-ℤ s t k) (H k))
```

## Properties

### Characterization of the identity type of structure preserving dependent maps from the integers

```agda
module _
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k ≃ (P (succ-ℤ k))))
  where

  Eq-ELIM-ℤ : (s t : ELIM-ℤ P p0 pS) → UU l1
  Eq-ELIM-ℤ s t =
    ELIM-ℤ
      ( λ k → Id (pr1 s k) (pr1 t k))
      ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
      ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)

  reflexive-Eq-ELIM-ℤ : (s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ s s
  pr1 (reflexive-Eq-ELIM-ℤ (f , p , H)) = refl-htpy
  pr1 (pr2 (reflexive-Eq-ELIM-ℤ (f , p , H))) = inv (right-inv p)
  pr2 (pr2 (reflexive-Eq-ELIM-ℤ (f , p , H))) = inv ∘ (right-inv ∘ H)

  Eq-ELIM-ℤ-eq :
    ( s t : ELIM-ℤ P p0 pS) → (s ＝ t) → Eq-ELIM-ℤ s t
  Eq-ELIM-ℤ-eq s .s refl = reflexive-Eq-ELIM-ℤ s

  abstract
    is-contr-total-Eq-ELIM-ℤ :
      ( s : ELIM-ℤ P p0 pS) → is-contr (Σ (ELIM-ℤ P p0 pS) (Eq-ELIM-ℤ s))
    is-contr-total-Eq-ELIM-ℤ s =
      is-contr-total-Eq-structure
        ( λ f t H →
          ( zero-Eq-ELIM-ℤ P p0 pS s (pair f t) H) ×
          ( succ-Eq-ELIM-ℤ P p0 pS s (pair f t) H))
        ( is-contr-total-htpy (pr1 s))
        ( pair (pr1 s) refl-htpy)
        ( is-contr-total-Eq-structure
          ( λ p K
            ( q : zero-Eq-ELIM-ℤ P p0 pS s
              ( pair (pr1 s) (pair p K))
              ( refl-htpy)) →
            succ-Eq-ELIM-ℤ P p0 pS s
              ( pair (pr1 s) (pair p K))
              ( refl-htpy))
          ( is-contr-is-equiv'
            ( Σ (Id (pr1 s zero-ℤ) p0) (λ α → Id α (pr1 (pr2 s))))
            ( tot (λ α → con-inv refl α (pr1 (pr2 s))))
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ α → is-equiv-con-inv refl α (pr1 (pr2 s))))
            ( is-contr-total-path' (pr1 (pr2 s))))
          ( pair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
          ( is-contr-is-equiv'
            ( Σ ( ( k : ℤ) → Id (pr1 s (succ-ℤ k)) (pr1 (pS k) (pr1 s k)))
                ( λ β → β ~ (pr2 (pr2 s))))
            ( tot (λ β → con-inv-htpy refl-htpy β (pr2 (pr2 s))))
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ β → is-equiv-con-inv-htpy refl-htpy β (pr2 (pr2 s))))
            ( is-contr-total-htpy' (pr2 (pr2 s)))))

  abstract
    is-equiv-Eq-ELIM-ℤ-eq :
      ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq s t)
    is-equiv-Eq-ELIM-ℤ-eq s =
      fundamental-theorem-id
        ( is-contr-total-Eq-ELIM-ℤ s)
        ( Eq-ELIM-ℤ-eq s)

  eq-Eq-ELIM-ℤ :
    ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ s t → (s ＝ t)
  eq-Eq-ELIM-ℤ s t = map-inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq s t)

  abstract
    is-prop-ELIM-ℤ : is-prop (ELIM-ℤ P p0 pS)
    is-prop-ELIM-ℤ =
      is-prop-all-elements-equal
        ( λ s t → eq-Eq-ELIM-ℤ s t
          ( Elim-ℤ
            ( λ k → Id (pr1 s k) (pr1 t k))
            ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
            ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)))
```

### The dependent universal property of the integers

```agda
  abstract
    is-contr-ELIM-ℤ : is-contr (ELIM-ℤ P p0 pS)
    is-contr-ELIM-ℤ =
      is-proof-irrelevant-is-prop
        ( is-prop-ELIM-ℤ)
        ( Elim-ℤ P p0 pS)
```

### The universal property of the integers

The universal property is just a special case of the dependent universal
property.

```agda
module _
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X)
  where

  ELIM-ℤ' : UU l1
  ELIM-ℤ' = ELIM-ℤ (λ k → X) x (λ k → e)

  abstract
    universal-property-ℤ : is-contr ELIM-ℤ'
    universal-property-ℤ = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)
```
