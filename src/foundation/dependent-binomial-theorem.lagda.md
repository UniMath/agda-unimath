# The dependent binomial theorem for types (distributivity of dependent function types over coproduct types)

```agda
module foundation.dependent-binomial-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-decompositions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.univalence

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  fam-coproduct :
    Fin 2 → UU (l1 ⊔ l2)
  fam-coproduct (inl (inr _)) = raise l2 A
  fam-coproduct (inr _) = raise l1 B

  map-compute-total-fam-coproduct :
    Σ (Fin 2) fam-coproduct → A + B
  map-compute-total-fam-coproduct (inl (inr _) , y) = inl (map-inv-raise y)
  map-compute-total-fam-coproduct (inr _ , y) = inr (map-inv-raise y)

  map-inv-compute-total-fam-coproduct :
    A + B → Σ (Fin 2) fam-coproduct
  pr1 (map-inv-compute-total-fam-coproduct (inl x)) = zero-Fin 1
  pr2 (map-inv-compute-total-fam-coproduct (inl x)) = map-raise x
  pr1 (map-inv-compute-total-fam-coproduct (inr x)) = one-Fin 1
  pr2 (map-inv-compute-total-fam-coproduct (inr x)) = map-raise x

  is-section-map-inv-compute-total-fam-coproduct :
    is-section
      ( map-compute-total-fam-coproduct)
      ( map-inv-compute-total-fam-coproduct)
  is-section-map-inv-compute-total-fam-coproduct (inl x) =
    ap inl (is-retraction-map-inv-raise {l2} x)
  is-section-map-inv-compute-total-fam-coproduct (inr x) =
    ap inr (is-retraction-map-inv-raise {l1} x)

  is-retraction-map-inv-compute-total-fam-coproduct :
    is-retraction
      ( map-compute-total-fam-coproduct)
      ( map-inv-compute-total-fam-coproduct)
  is-retraction-map-inv-compute-total-fam-coproduct (inl (inr _) , y) =
    eq-pair-eq-fiber (is-section-map-inv-raise y)
  is-retraction-map-inv-compute-total-fam-coproduct (inr _ , y) =
    eq-pair-eq-fiber (is-section-map-inv-raise y)

  is-equiv-map-compute-total-fam-coproduct :
    is-equiv map-compute-total-fam-coproduct
  is-equiv-map-compute-total-fam-coproduct =
    is-equiv-is-invertible
      map-inv-compute-total-fam-coproduct
      is-section-map-inv-compute-total-fam-coproduct
      is-retraction-map-inv-compute-total-fam-coproduct

  compute-total-fam-coproduct :
    (Σ (Fin 2) fam-coproduct) ≃ (A + B)
  pr1 compute-total-fam-coproduct = map-compute-total-fam-coproduct
  pr2 compute-total-fam-coproduct = is-equiv-map-compute-total-fam-coproduct

  inv-compute-total-fam-coproduct :
    (A + B) ≃ Σ (Fin 2) fam-coproduct
  inv-compute-total-fam-coproduct =
    inv-equiv compute-total-fam-coproduct

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  type-distributive-Π-coproduct : UU (l1 ⊔ l2 ⊔ l3)
  type-distributive-Π-coproduct =
    Σ ( X → Fin 2)
      ( λ f →
        ((x : X) (p : is-zero-Fin 2 (f x)) → A x) ×
        ((x : X) (p : is-one-Fin 2 (f x)) → B x))

  distributive-Π-coproduct :
    ((x : X) → A x + B x) ≃ type-distributive-Π-coproduct
  distributive-Π-coproduct =
    ( equiv-tot
      ( λ f →
        ( equiv-product
          ( equiv-Π-equiv-family
            ( λ x →
              equiv-Π-equiv-family
                ( λ p →
                  ( inv-equiv (compute-raise l3 (A x))) ∘e
                  ( equiv-tr (fam-coproduct (A x) (B x)) p))))
          ( equiv-Π-equiv-family
            ( λ x →
              equiv-Π-equiv-family
                ( λ p →
                  ( inv-equiv (compute-raise l2 (B x))) ∘e
                  ( equiv-tr (fam-coproduct (A x) (B x)) p))))) ∘e
        ( distributive-Π-Σ) ∘e
        ( equiv-Π-equiv-family
          ( λ x →
            ( equiv-universal-property-coproduct
              ( fam-coproduct (A x) (B x) (f x))) ∘e
            ( equiv-diagonal-exponential-is-contr
              ( fam-coproduct (A x) (B x) (f x))
              ( is-contr-is-zero-or-one-Fin-2 (f x))))))) ∘e
    ( distributive-Π-Σ) ∘e
    ( equiv-Π-equiv-family
      ( λ x → inv-compute-total-fam-coproduct (A x) (B x)))

  type-distributive-Π-coproduct-binary-coproduct-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l1 ⊔ lsuc l1)
  type-distributive-Π-coproduct-binary-coproduct-Decomposition =
    Σ ( binary-coproduct-Decomposition l1 l1 X)
      ( λ d →
        ( (u : left-summand-binary-coproduct-Decomposition d) →
          ( A
            ( map-inv-matching-correspondence-binary-coproduct-Decomposition d
              ( inl u)))) ×
        ( ( v : right-summand-binary-coproduct-Decomposition d) →
          ( B
            ( map-inv-matching-correspondence-binary-coproduct-Decomposition d
              ( inr v)))))

  equiv-type-distributive-Π-coproduct-binary-coproduct-Decomposition :
    type-distributive-Π-coproduct ≃
    type-distributive-Π-coproduct-binary-coproduct-Decomposition
  equiv-type-distributive-Π-coproduct-binary-coproduct-Decomposition =
    equiv-Σ
      ( λ d →
        ( (u : left-summand-binary-coproduct-Decomposition d) →
          A ( map-inv-matching-correspondence-binary-coproduct-Decomposition d
              ( inl u))) ×
        ( (v : right-summand-binary-coproduct-Decomposition d) →
          B ( map-inv-matching-correspondence-binary-coproduct-Decomposition d
              ( inr v))))
      ( equiv-binary-coproduct-Decomposition-map-into-Fin-2)
      ( λ f →
        equiv-product
          ( equiv-Π-equiv-family
            ( λ a →
              equiv-eq
                ( ap
                  ( A)
                  ( compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2
                    ( f)
                    ( a)))) ∘e
            inv-equiv equiv-ev-pair)
          ( equiv-Π-equiv-family
            ( λ a →
              equiv-eq
                ( ap
                  ( B)
                  ( compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2
                    ( f)
                    ( a)))) ∘e
            inv-equiv equiv-ev-pair))

  distributive-Π-coproduct-binary-coproduct-Decomposition :
    ((x : X) → A x + B x) ≃
    type-distributive-Π-coproduct-binary-coproduct-Decomposition
  distributive-Π-coproduct-binary-coproduct-Decomposition =
    equiv-type-distributive-Π-coproduct-binary-coproduct-Decomposition ∘e
    distributive-Π-coproduct
```
