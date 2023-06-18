# Falling factorials

```agda
module elementary-number-theory.falling-factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The falling factorial (n)\_m is the number n(n-1)⋯(n-m+1)

## Definition

```agda
falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = 1
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = 0
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = 1
falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  (succ-ℕ n) *ℕ (falling-factorial-ℕ n m)

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ n m = {!!}
-}

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ zero-ℕ zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb id)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' empty)
        ( id))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap id))))
Fin-falling-factorial-ℕ zero-ℕ (succ-ℕ m) =
  equiv-is-empty id (λ f → map-emb f (inr star))
Fin-falling-factorial-ℕ (succ-ℕ n) zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb ex-falso)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' (Fin (succ-ℕ n)))
        ( ex-falso))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap ex-falso))))
Fin-falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  ( ( ( right-unit-law-Σ-is-contr
        { B = λ f → is-decidable (fib (map-emb f) (inr star))}
        ( λ f →
          is-proof-irrelevant-is-prop
            ( is-prop-is-decidable
              ( is-prop-map-is-emb (is-emb-map-emb f) (inr star)))
            ( is-decidable-Σ-Fin
              ( λ x →
                has-decidable-equality-Fin (map-emb f x) (inr star))))) ∘e
      ( ( inv-equiv
          ( left-distributive-Σ-coprod
            ( Fin (succ-ℕ m) ↪ Fin (succ-ℕ n))
            ( λ f → fib (map-emb f) (inr star))
            ( λ f → ¬ (fib (map-emb f) (inr star))))) ∘e
        {!!})) ∘e
    ( equiv-coprod
      ( Fin-falling-factorial-ℕ n m)
      ( Fin-falling-factorial-ℕ n (succ-ℕ m)))) ∘e
  ( Fin-add-ℕ (falling-factorial-ℕ n m) (falling-factorial-ℕ n (succ-ℕ m)))
-}
```
