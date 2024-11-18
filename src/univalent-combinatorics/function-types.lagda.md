# Finite function types

```agda
module univalent-combinatorics.function-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Properties

### The type of functions between types equipped with a counting can be equipped with a counting

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (c : count A) (d : count B)
  where

  count-function-type : count (A → B)
  count-function-type = count-Π c (λ _ → d)

  number-of-elements-count-function-type :
    number-of-elements-count count-function-type ＝
    exp-ℕ (number-of-elements-count d) (number-of-elements-count c)
  number-of-elements-count-function-type =
    number-of-elements-count-Π c (λ _ → d) ∙
    compute-constant-product-ℕ
      ( number-of-elements-count d)
      ( number-of-elements-count c)
```

### The type of functions between finite types is finite

```agda
abstract
  is-finite-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A → B)
  is-finite-function-type f g = is-finite-Π f (λ x → g)

  number-of-elements-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (H : is-finite A) (K : is-finite B) →
    number-of-elements-is-finite (is-finite-function-type H K) ＝
    exp-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H)
  number-of-elements-function-type H K =
    apply-twice-universal-property-trunc-Prop H K
      ( Id-Prop ℕ-Set _ _)
      ( λ c d →
        inv
          ( compute-number-of-elements-is-finite
            ( count-function-type c d)
            ( is-finite-function-type H K)) ∙
        number-of-elements-count-function-type c d ∙
        ap-binary
          ( exp-ℕ)
          ( compute-number-of-elements-is-finite d K)
          ( compute-number-of-elements-is-finite c H))

_→-𝔽_ : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (A →-𝔽 B) = type-𝔽 A → type-𝔽 B
pr2 (A →-𝔽 B) =
  is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)
```

### The type of equivalences between finite types is finite

```agda
abstract
  is-finite-≃ :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A ≃ B)
  is-finite-≃ f g =
    is-finite-Σ
      ( is-finite-function-type f g)
      ( λ h →
        is-finite-product
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π g
                ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π f
                ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

infix 6 _≃-𝔽_
_≃-𝔽_ : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (A ≃-𝔽 B) = type-𝔽 A ≃ type-𝔽 B
pr2 (A ≃-𝔽 B) = is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)
```

### The type of automorphisms on a finite type is finite

```agda
Aut-𝔽 : {l : Level} → 𝔽 l → 𝔽 l
Aut-𝔽 A = A ≃-𝔽 A
```
