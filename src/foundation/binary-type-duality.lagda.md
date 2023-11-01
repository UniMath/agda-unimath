# Binary type duality

```agda
module foundation.binary-type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-spans
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.spans
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Using the principles of [type duality](foundation.type-duality.md) and
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md),
we can show that the type of spans `A <-- S --> B` is
[equivalent](foundation.equivalences.md) to the type of type-valued binary
relations `A → B → 𝓤`.

## Theorem

### Binary spans with fixed domain and codomain are equivalent to binary relations

```agda
module _
  { l1 l2 l : Level} (A : UU l1) (B : UU l2)
  where

  binary-type-duality :
    ( A → B → UU (l1 ⊔ l2 ⊔ l)) ≃ span-fixed-domain-codomain (l1 ⊔ l2 ⊔ l) A B
  binary-type-duality =
    ( associative-Σ (UU (l1 ⊔ l2 ⊔ l)) (λ X → X → A) (λ T → pr1 T → B)) ∘e
    ( equiv-Σ (λ T → pr1 T → B) (equiv-Pr1 (l2 ⊔ l) A) (λ P → equiv-ind-Σ)) ∘e
    ( distributive-Π-Σ) ∘e
    ( equiv-Π-equiv-family (λ a → equiv-Pr1 (l1 ⊔ l) B))

  span-fixed-domain-codomain-binary-relation :
    (A → B → UU (l1 ⊔ l2 ⊔ l)) → span-fixed-domain-codomain (l1 ⊔ l2 ⊔ l) A B
  pr1 (span-fixed-domain-codomain-binary-relation R) =
    Σ A (λ a → Σ B (λ b → R a b))
  pr1 (pr2 (span-fixed-domain-codomain-binary-relation R)) =
    pr1
  pr2 (pr2 (span-fixed-domain-codomain-binary-relation R)) =
    pr1 ∘ pr2

  compute-span-fixed-domain-codomain-binary-relation :
    map-equiv binary-type-duality ~
    span-fixed-domain-codomain-binary-relation
  compute-span-fixed-domain-codomain-binary-relation = refl-htpy

  binary-relation-span-fixed-domain-codomain :
    span-fixed-domain-codomain (l1 ⊔ l2 ⊔ l) A B → (A → B → UU (l1 ⊔ l2 ⊔ l))
  binary-relation-span-fixed-domain-codomain S a b =
    Σ ( spanning-type-span-fixed-domain-codomain S)
      ( λ s →
        ( left-map-span-fixed-domain-codomain S s ＝ a) ×
        ( right-map-span-fixed-domain-codomain S s ＝ b))

  compute-binary-relation-span-fixed-domain-codomain :
    map-inv-equiv binary-type-duality ~
    binary-relation-span-fixed-domain-codomain
  compute-binary-relation-span-fixed-domain-codomain S =
    inv
      ( map-eq-transpose-equiv binary-type-duality
        ( eq-equiv-span-fixed-domain-codomain _ _
          ( ( ( equiv-pr1
                ( λ s →
                  is-torsorial-path
                    ( left-map-span-fixed-domain-codomain S s))) ∘e
              ( equiv-left-swap-Σ) ∘e
              ( equiv-tot
                ( λ a →
                  ( equiv-tot
                    ( λ s →
                      ( equiv-pr1
                        ( λ _ →
                          is-torsorial-path
                            ( right-map-span-fixed-domain-codomain S s))) ∘e
                      ( equiv-left-swap-Σ))) ∘e
                  ( equiv-left-swap-Σ)))) ,
            ( inv-htpy (pr1 ∘ pr2 ∘ pr2 ∘ pr2)) ,
            ( inv-htpy (pr2 ∘ pr2 ∘ pr2 ∘ pr2)))))
```
