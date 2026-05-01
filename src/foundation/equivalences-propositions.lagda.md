# Equivalences between propositions

```agda
module foundation.equivalences-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Properties

### The type of equivalences between two propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop H K =
    is-prop-Σ
      ( is-prop-function-type K)
      ( λ f →
        is-prop-product
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ g → is-prop-is-contr (is-contr-Π (λ y → K (f (g y)) y))))
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ h → is-prop-is-contr (is-contr-Π (λ x → H (h (f x)) x)))))

type-equiv-Prop :
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

abstract
  is-prop-type-equiv-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-equiv-Prop P Q)
  is-prop-type-equiv-Prop P Q =
    is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (equiv-Prop P Q) = type-equiv-Prop P Q
pr2 (equiv-Prop P Q) = is-prop-type-equiv-Prop P Q
```
