# The subuniverse of `k`-truncated types

```agda
module foundation.subuniverse-of-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subuniverse-of-contractible-types
open import foundation-core.truncated-types
```

</details>

## Idea

The condition that a type is [`k`-truncated](foundation-core.truncated-types.md)
is a [property](foundation-core.propositions.md). Thus, the `k`-truncated types
form a [subuniverse](foundation.subuniverses.md).

## Definitions

### The subuniverse of `k`-truncated types

```agda
abstract
  is-property-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-property-is-trunc neg-two-𝕋 A = is-property-is-contr
  is-property-is-trunc (succ-𝕋 k) A =
    is-trunc-Π neg-one-𝕋
      ( λ x → is-trunc-Π neg-one-𝕋 (λ y → is-property-is-trunc k (x ＝ y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → Σ (UU l) (is-trunc neg-one-𝕋)
pr1 (is-trunc-Prop k A) = is-trunc k A
pr2 (is-trunc-Prop k A) = is-property-is-trunc k A
```
