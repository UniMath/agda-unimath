# The dependent binomial theorem for types (Distributivity of dependent function types over coproduct types)

```agda
module foundation.dependent-binomial-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  fam-coprod :
    Fin 2  → UU (l1 ⊔ l2)
  fam-coprod (inl (inr star)) = raise l2 A
  fam-coprod (inr star) = raise l1 B

  map-compute-total-fam-coprod :
    Σ (Fin 2) fam-coprod → A + B
  map-compute-total-fam-coprod (pair (inl (inr star)) y) = inl (map-inv-raise y)
  map-compute-total-fam-coprod (pair (inr star) y) = inr (map-inv-raise y)

  map-inv-compute-total-fam-coprod :
    A + B → Σ (Fin 2) fam-coprod
  pr1 (map-inv-compute-total-fam-coprod (inl x)) = zero-Fin 1
  pr2 (map-inv-compute-total-fam-coprod (inl x)) = map-raise x
  pr1 (map-inv-compute-total-fam-coprod (inr x)) = one-Fin 1
  pr2 (map-inv-compute-total-fam-coprod (inr x)) = map-raise x

  issec-map-inv-compute-total-fam-coprod :
    (map-compute-total-fam-coprod ∘ map-inv-compute-total-fam-coprod) ~ id
  issec-map-inv-compute-total-fam-coprod (inl x) =
    ap inl (isretr-map-inv-raise {l2} x)
  issec-map-inv-compute-total-fam-coprod (inr x) =
    ap inr (isretr-map-inv-raise {l1} x)

  isretr-map-inv-compute-total-fam-coprod :
    (map-inv-compute-total-fam-coprod ∘ map-compute-total-fam-coprod) ~ id
  isretr-map-inv-compute-total-fam-coprod (pair (inl (inr star)) y) =
    ap (pair (zero-Fin 1)) (issec-map-inv-raise y)
  isretr-map-inv-compute-total-fam-coprod (pair (inr star) y) =
    ap (pair (one-Fin 1)) (issec-map-inv-raise y)

  is-equiv-map-compute-total-fam-coprod :
    is-equiv map-compute-total-fam-coprod
  is-equiv-map-compute-total-fam-coprod =
    is-equiv-has-inverse
      map-inv-compute-total-fam-coprod
      issec-map-inv-compute-total-fam-coprod
      isretr-map-inv-compute-total-fam-coprod

  compute-total-fam-coprod :
    (Σ (Fin 2) fam-coprod) ≃ (A + B)
  pr1 compute-total-fam-coprod = map-compute-total-fam-coprod
  pr2 compute-total-fam-coprod = is-equiv-map-compute-total-fam-coprod

  inv-compute-total-fam-coprod :
    (A + B) ≃ Σ (Fin 2) fam-coprod
  inv-compute-total-fam-coprod =
    inv-equiv compute-total-fam-coprod

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  type-distributive-Π-coprod : UU (l1 ⊔ l2 ⊔ l3)
  type-distributive-Π-coprod =
    Σ ( X → Fin 2)
      ( λ f → ((x : X) (p : is-zero-Fin 2 (f x)) → A x) ×
              ((x : X) (p : is-one-Fin 2 (f x)) → B x))

  distributive-Π-coprod :
    ((x : X) → A x + B x) ≃ type-distributive-Π-coprod
  distributive-Π-coprod =
    ( ( equiv-tot
        ( λ f →
          ( ( equiv-prod
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (compute-raise l3 (A x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (compute-raise l2 (B x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))) ∘e
            ( distributive-Π-Σ)) ∘e
          ( equiv-map-Π
            ( λ x →
              ( equiv-universal-property-coprod
                ( fam-coprod (A x) (B x) (f x))) ∘e
              ( equiv-diagonal-is-contr
                ( fam-coprod (A x) (B x) (f x))
                ( is-contr-is-zero-or-one-Fin-two-ℕ (f x))))))) ∘e
      ( distributive-Π-Σ)) ∘e
    ( equiv-map-Π
      ( λ x → inv-compute-total-fam-coprod (A x) (B x)))
```
