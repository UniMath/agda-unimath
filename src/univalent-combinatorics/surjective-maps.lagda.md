# Surjective maps between finite types

```agda
module univalent-combinatorics.surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.embeddings
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.dependent-sum-finite-types
open import foundation.surjective-maps public
open import foundation.cartesian-product-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
```

</details>

## Properties

```agda
is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fib f HA HB y))
```

### If `X` has decidable equality and there exist a surjection  `Fin-n ↠ X` then `X` has a counting

```agda
module _
  {l1 l2 : Level} {X : UU l1 }
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
            (Σ _ (fib (pr1 f))) )
          ( tot-decidable-emb-trunc-Prop-count
            { P = fib (map-surjection f)}
            ( count-fiber-count-Σ
              dec-X
              ( count-equiv
                ( inv-equiv-total-fib (map-surjection f)) (count-Fin n))))))
      ( count-equiv (inv-equiv-total-fib (map-surjection f)) (count-Fin n))

  is-finite-iff-∃-surjection-has-decidable-equality :
    is-finite X ≃
      ( has-decidable-equality X × type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
  is-finite-iff-∃-surjection-has-decidable-equality =
    equiv-prop
      ( is-prop-is-finite X)
      ( is-prop-prod is-prop-has-decidable-equality is-prop-type-trunc-Prop)
      ( λ fin-X →
        apply-universal-property-trunc-Prop
          ( fin-X)
          ( prod-Prop (has-decidable-equality-Prop X) (trunc-Prop _))
          ( λ count-X →
            ( has-decidable-equality-count count-X  ,
              unit-trunc-Prop
                ( pr1 count-X ,
                  ( map-equiv (pr2 count-X)) ,
                    ( is-surjective-map-equiv (pr2 count-X))))))
      ( λ dec-X-surj →
        apply-universal-property-trunc-Prop
          ( pr2 dec-X-surj)
          ( is-finite-Prop X)
          ( λ n-surj →
            unit-trunc-Prop
              ( count-surjection-has-decidable-equality
                ( pr1 n-surj)
                ( pr1 dec-X-surj)
                ( pr2 n-surj))))

```

-- ### Type duality surjective function between finite type

-- If `A` and `B` are finite, then surjective maps from `A → B` is equivalent to the type of pairs of inhabited dependent family `Y : A → 𝔽` and equivalence between `A ≃ Σ B Y`

-- ```agda
-- type-duality-surjective-functions-𝔽 :
--   {l1 : Level} (l2 : Level) (A : 𝔽 l1) (B : 𝔽 (l1 ⊔ l2))→
--   ((type-𝔽 A) ↠ (type-𝔽 B)) ≃
--     Σ
--     ( Fam-Inhabited-Types-𝔽 (l1 ⊔ l2) B )
--     ( λ Y → type-𝔽 A ≃ Σ (type-𝔽 B) λ x → type-Fam-Inhabited-Types-𝔽 B Y x)
-- type-duality-surjective-functions-𝔽 {l1} l2 A B =
--   ( ( equiv-Σ-equiv-base
--       ( λ Y → type-𝔽 A ≃ Σ (type-𝔽 B) ( type-Fam-Inhabited-Types-𝔽 B Y))
--       ( inv-equiv (equiv-Fam-Inhabited-Type-𝔽 B))) ∘e
--     ( ( inv-assoc-Σ _  _ _ ) ∘e
--         ( ( equiv-Σ
--             ( _)
--             ( id-equiv)
--             ( λ Y →
--               ( ( equiv-Σ
--                   ( _)
--                   ( id-equiv)
--                   ( λ f →
--                     {!id-equiv!})) ∘e
--                 commutative-prod) ∘e
--                 inv-equiv
--                   ( right-unit-law-Σ-is-contr
--                     ( λ e →
--                       ( is-proof-irrelevant-is-prop
--                         ( is-prop-Π
--                           ( λ x → is-prop-is-finite (type-Inhabited-Type (Y x))))
--                         ( is-finite-fiber-is-finite-Σ
--                           ( is-finite-type-𝔽 B)
--                           ( is-finite-equiv e (is-finite-type-𝔽 A))))))))  ∘e
--           ( type-duality-surjective-functions l2 (type-𝔽 A) (type-𝔽 B)))))
-- ```

