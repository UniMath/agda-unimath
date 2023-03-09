# Powersets

```agda
module foundation.powersets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definition

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = subtype

module _
  {l1 : Level} {A : UU l1}
  where

  inclusion-rel-subtype-Prop :
    {l2 l3 : Level} → subtype l2 A → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  inclusion-rel-subtype-Prop P Q =
    Π-Prop A (λ x → hom-Prop (P x) (Q x))

  _⊆_ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  P ⊆ Q = type-Prop (inclusion-rel-subtype-Prop P Q)

  is-prop-inclusion-rel-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → is-prop (P ⊆ Q)
  is-prop-inclusion-rel-subtype P Q =
    is-prop-type-Prop (inclusion-rel-subtype-Prop P Q)
```

## Properties

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  refl-⊆ : {l2 : Level} (P : subtype l2 A) → P ⊆ P
  refl-⊆ P x = id

  trans-⊆ :
    {l2 l3 l4 : Level}
    (P : subtype l2 A) (Q : subtype l3 A) (R : subtype l4 A) →
    Q ⊆ R → P ⊆ Q → P ⊆ R
  trans-⊆ P Q R H K x = H x ∘ K x

  equiv-antisymmetric-⊆ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → P ⊆ Q → Q ⊆ P →
    (x : A) → is-in-subtype P x ≃ is-in-subtype Q x
  equiv-antisymmetric-⊆ P Q H K x =
    equiv-prop
      ( is-prop-is-in-subtype P x)
      ( is-prop-is-in-subtype Q x)
      ( H x)
      ( K x)

  antisymmetric-⊆ :
    {l2 : Level} (P Q : subtype l2 A) → P ⊆ Q → Q ⊆ P → P ＝ Q
  antisymmetric-⊆ P Q H K = eq-htpy (λ x → eq-iff (H x) (K x))
```

### The powerset preorder and poset

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Preorder :
    Large-Preorder (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder powerset-Large-Preorder l = subtype l A
  leq-large-preorder-Prop powerset-Large-Preorder = inclusion-rel-subtype-Prop
  refl-leq-Large-Preorder powerset-Large-Preorder = refl-⊆
  trans-leq-Large-Preorder powerset-Large-Preorder = trans-⊆

  powerset-Preorder : (l2 : Level) → Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Preorder = preorder-Large-Preorder powerset-Large-Preorder

  powerset-Large-Poset :
    Large-Poset (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset powerset-Large-Poset = powerset-Large-Preorder
  antisymmetric-leq-Large-Poset powerset-Large-Poset = antisymmetric-⊆

  powerset-Poset : (l2 : Level) → Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Poset = poset-Large-Poset powerset-Large-Poset
```
