# Dependent products truncated types

```agda
module foundation.dependent-products-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Given a family of $n$-[truncated](foundation-core.truncated-types.md)
`B : A → 𝒰`, then the dependent product `Π A B` is again $n$-truncated.

## Properties

### Products of families of truncated types are truncated

```agda
abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k (f ~ g) htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type' k A B = (x : A) → type-Truncated-Type (B x)

is-trunc-type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  is-trunc k (type-Π-Truncated-Type' k A B)
is-trunc-type-Π-Truncated-Type' k A B =
  is-trunc-Π k (λ x → is-trunc-type-Truncated-Type (B x))

Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (Π-Truncated-Type' k A B) = type-Π-Truncated-Type' k A B
pr2 (Π-Truncated-Type' k A B) = is-trunc-type-Π-Truncated-Type' k A B

type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type k A B =
  type-Π-Truncated-Type' k (type-Truncated-Type A) B

is-trunc-type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  is-trunc k (type-Π-Truncated-Type k A B)
is-trunc-type-Π-Truncated-Type k A B =
  is-trunc-type-Π-Truncated-Type' k (type-Truncated-Type A) B

Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
Π-Truncated-Type k A B =
  Π-Truncated-Type' k (type-Truncated-Type A) B
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

function-type-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (function-type-Truncated-Type A B) = A → type-Truncated-Type B
pr2 (function-type-Truncated-Type A B) =
  is-trunc-function-type _ (is-trunc-type-Truncated-Type B)

type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) → UU (l1 ⊔ l2)
type-hom-Truncated-Type k A B =
  type-Truncated-Type A → type-Truncated-Type B

is-trunc-type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) →
  is-trunc k (type-hom-Truncated-Type k A B)
is-trunc-type-hom-Truncated-Type k A B =
  is-trunc-function-type k (is-trunc-type-Truncated-Type B)

hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) → Truncated-Type (l1 ⊔ l2) k
pr1 (hom-Truncated-Type k A B) = type-hom-Truncated-Type k A B
pr2 (hom-Truncated-Type k A B) = is-trunc-type-hom-Truncated-Type k A B
```

### Being truncated is a property

```agda
abstract
  is-prop-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-prop-is-trunc neg-two-𝕋 A = is-property-is-contr
  is-prop-is-trunc (succ-𝕋 k) A =
    is-trunc-Π neg-one-𝕋
      ( λ x → is-trunc-Π neg-one-𝕋 (λ y → is-prop-is-trunc k (x ＝ y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → Σ (UU l) (is-trunc neg-one-𝕋)
pr1 (is-trunc-Prop k A) = is-trunc k A
pr2 (is-trunc-Prop k A) = is-prop-is-trunc k A
```

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc k H K =
    is-trunc-Σ
      ( is-trunc-function-type k K)
      ( λ f →
        is-trunc-Σ
          ( is-trunc-Σ
            ( is-trunc-function-type k H)
            ( λ g →
              is-trunc-Π k (λ y → is-trunc-Id K (f (g y)) y)))
          ( λ _ →
            is-trunc-Σ
              ( is-trunc-function-type k H)
              ( λ h →
                is-trunc-Π k (λ x → is-trunc-Id H (h (f x)) x))))

type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-equiv-Truncated-Type A B =
  type-Truncated-Type A ≃ type-Truncated-Type B

is-trunc-type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  is-trunc k (type-equiv-Truncated-Type A B)
is-trunc-type-equiv-Truncated-Type A B =
  is-trunc-equiv-is-trunc _
    ( is-trunc-type-Truncated-Type A)
    ( is-trunc-type-Truncated-Type B)

equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (equiv-Truncated-Type A B) = type-equiv-Truncated-Type A B
pr2 (equiv-Truncated-Type A B) = is-trunc-type-equiv-Truncated-Type A B
```
