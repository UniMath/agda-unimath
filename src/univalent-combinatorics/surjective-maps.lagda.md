# Surjective maps between finite types

```agda
module univalent-combinatorics.surjective-maps where

open import foundation.surjective-maps public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.embeddings
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

```agda
Surjection-𝔽 :
  {l1 : Level} (l2 : Level) → 𝔽 l1 → UU (l1 ⊔ lsuc l2)
Surjection-𝔽 l2 A =
  Σ (𝔽 l2) (λ B → (type-𝔽 A) ↠ (type-𝔽 B))
```

## Properties

```agda
is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fiber f HA HB y))
```

### If `X` has decidable equality and there exist a surjection `Fin-n ↠ X` then `X` has a counting

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  count-surjection-has-decidable-equality :
    (n : ℕ) → (has-decidable-equality X) → (Fin n ↠ X) →
    count (X)
  count-surjection-has-decidable-equality n dec-X f =
    count-decidable-emb
      ( ( map-equiv
          ( equiv-precomp-decidable-emb-equiv
            ( inv-equiv
              ( right-unit-law-Σ-is-contr
                ( λ x →
                  is-proof-irrelevant-is-prop
                    ( is-prop-type-trunc-Prop)
                    ( is-surjective-map-surjection f x))))
            (Σ _ (fiber (pr1 f))))
          ( decidable-emb-tot-trunc-Prop-count
            { P = fiber (map-surjection f)}
            ( count-fiber-count-Σ
              dec-X
              ( count-equiv
                ( inv-equiv-total-fiber (map-surjection f)) (count-Fin n))))))
      ( count-equiv (inv-equiv-total-fiber (map-surjection f)) (count-Fin n))
```

### A type `X` is finite if and only if it has decidable equality and there exists a surjection from a finite type to `X`

```agda
  is-finite-if-∃-surjection-has-decidable-equality :
    is-finite X →
    ( has-decidable-equality X × type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
  is-finite-if-∃-surjection-has-decidable-equality fin-X =
    apply-universal-property-trunc-Prop
      ( fin-X)
      ( prod-Prop (has-decidable-equality-Prop X) (trunc-Prop _))
      ( λ count-X →
        ( has-decidable-equality-count count-X ,
          unit-trunc-Prop
          ( pr1 count-X ,
            ( map-equiv (pr2 count-X)) ,
            ( is-surjective-map-equiv (pr2 count-X)))))

  ∃-surjection-has-decidable-equality-if-is-finite :
    ( has-decidable-equality X × type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X))) →
    is-finite X
  ∃-surjection-has-decidable-equality-if-is-finite dec-X-surj =
    apply-universal-property-trunc-Prop
          ( pr2 dec-X-surj)
          ( is-finite-Prop X)
          ( λ n-surj →
            unit-trunc-Prop
              ( count-surjection-has-decidable-equality
                ( pr1 n-surj)
                ( pr1 dec-X-surj)
                ( pr2 n-surj)))

  is-finite-iff-∃-surjection-has-decidable-equality :
    is-finite X ≃
    ( has-decidable-equality X × type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
  is-finite-iff-∃-surjection-has-decidable-equality =
    equiv-prop
      ( is-prop-is-finite X)
      ( is-prop-prod is-prop-has-decidable-equality is-prop-type-trunc-Prop)
      ( λ fin-X → is-finite-if-∃-surjection-has-decidable-equality fin-X)
      ( λ dec-X-surj →
        ∃-surjection-has-decidable-equality-if-is-finite dec-X-surj)
```
