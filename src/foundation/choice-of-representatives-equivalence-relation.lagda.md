# Choice of representatives for an equivalence relation

```agda
module foundation.choice-of-representatives-equivalence-relation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
```

</details>

## Idea

If we can construct a choice of representatives for each equivalence class, then
we can construct the set quotient as a retract of the original type.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-choice-of-representatives :
    (A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-choice-of-representatives P =
    (a : A) → is-contr (Σ A (λ x → P x × sim-equivalence-relation R a x))

  representatives :
    {P : A → UU l3} → is-choice-of-representatives P → UU (l1 ⊔ l3)
  representatives {P} H = Σ A P

  class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H → equivalence-class R
  class-representatives H a =
    class R (pr1 a)

  abstract
    is-surjective-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-surjective (class-representatives H)
    is-surjective-class-representatives H (pair Q K) =
      apply-universal-property-trunc-Prop K
        ( trunc-Prop
          ( fiber (class-representatives H) (pair Q K)))
        ( λ (pair a φ) →
          unit-trunc-Prop
            ( pair
              ( pair (pr1 (center (H a))) (pr1 (pr2 (center (H a)))))
              ( ( apply-effectiveness-class' R
                  ( symmetric-equivalence-relation R _ _
                    ( pr2 (pr2 (center (H a)))))) ∙
                ( eq-class-equivalence-class R
                  ( pair Q K)
                  ( backward-implication
                    ( φ a)
                    ( refl-equivalence-relation R _))))))

  abstract
    is-emb-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-emb (class-representatives H)
    is-emb-class-representatives {P} H (pair a p) =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ A (λ x → P x × sim-equivalence-relation R a x))
          ( ( associative-Σ) ∘e
            ( equiv-tot (λ t → is-effective-class R a (pr1 t))))
          ( H a))
        ( λ y →
          ap (class-representatives H) {pair a p} {y})

  abstract
    is-equiv-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-equiv (class-representatives H)
    is-equiv-class-representatives H =
      is-equiv-is-emb-is-surjective
        ( is-surjective-class-representatives H)
        ( is-emb-class-representatives H)

  equiv-equivalence-class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H ≃ equivalence-class R
  pr1 (equiv-equivalence-class-representatives H) = class-representatives H
  pr2 (equiv-equivalence-class-representatives H) =
    is-equiv-class-representatives H
```
