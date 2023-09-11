# Subtypes

```agda
module foundation.subtypes where

open import foundation-core.subtypes public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Definition

### A second definition of the type of subtypes

```agda
Subtype : {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Subtype l2 l3 A =
  Σ ( A → Prop l2)
    ( λ P →
      Σ ( Σ (UU l3) (λ X → X ↪ A))
        ( λ i →
          Σ ( pr1 i ≃ Σ A (type-Prop ∘ P))
            ( λ e → map-emb (pr2 i) ~ (pr1 ∘ map-equiv e))))
```

## Properties

### The inclusion of a subtype into the ambient type is injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  is-injective-inclusion-subtype : is-injective (inclusion-subtype B)
  is-injective-inclusion-subtype =
    is-injective-is-emb (is-emb-inclusion-subtype B)
```

### Equality in the type of all subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  has-same-elements-subtype-Prop :
    {l3 : Level} → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype-Prop Q =
    Π-Prop A (λ x → iff-Prop (P x) (Q x))

  has-same-elements-subtype : {l3 : Level} → subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype Q = type-Prop (has-same-elements-subtype-Prop Q)

  is-prop-has-same-elements-subtype :
    {l3 : Level} (Q : subtype l3 A) →
    is-prop (has-same-elements-subtype Q)
  is-prop-has-same-elements-subtype Q =
    is-prop-type-Prop (has-same-elements-subtype-Prop Q)

  refl-has-same-elements-subtype : has-same-elements-subtype P
  pr1 (refl-has-same-elements-subtype x) = id
  pr2 (refl-has-same-elements-subtype x) = id

  is-contr-total-has-same-elements-subtype :
    is-contr (Σ (subtype l2 A) has-same-elements-subtype)
  is-contr-total-has-same-elements-subtype =
    is-contr-total-Eq-Π
      ( λ x Q → P x ⇔ Q)
      ( λ x → is-contr-total-iff (P x))

  has-same-elements-eq-subtype :
    (Q : subtype l2 A) → (P ＝ Q) → has-same-elements-subtype Q
  has-same-elements-eq-subtype .P refl =
    refl-has-same-elements-subtype

  is-equiv-has-same-elements-eq-subtype :
    (Q : subtype l2 A) → is-equiv (has-same-elements-eq-subtype Q)
  is-equiv-has-same-elements-eq-subtype =
    fundamental-theorem-id
      is-contr-total-has-same-elements-subtype
      has-same-elements-eq-subtype

  extensionality-subtype :
    (Q : subtype l2 A) → (P ＝ Q) ≃ has-same-elements-subtype Q
  pr1 (extensionality-subtype Q) = has-same-elements-eq-subtype Q
  pr2 (extensionality-subtype Q) = is-equiv-has-same-elements-eq-subtype Q

  eq-has-same-elements-subtype :
    (Q : subtype l2 A) → has-same-elements-subtype Q → P ＝ Q
  eq-has-same-elements-subtype Q =
    map-inv-equiv (extensionality-subtype Q)
```

### The containment relation is antisymmetric

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  equiv-antisymmetric-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → P ⊆ Q → Q ⊆ P →
    (x : A) → is-in-subtype P x ≃ is-in-subtype Q x
  equiv-antisymmetric-leq-subtype P Q H K x =
    equiv-prop
      ( is-prop-is-in-subtype P x)
      ( is-prop-is-in-subtype Q x)
      ( H x)
      ( K x)

  antisymmetric-leq-subtype :
    {l2 : Level} (P Q : subtype l2 A) → P ⊆ Q → Q ⊆ P → P ＝ Q
  antisymmetric-leq-subtype P Q H K =
    eq-has-same-elements-subtype P Q (λ x → (H x , K x))
```

### The type of all subtypes of a type is a set

```agda
is-set-subtype :
  {l1 l2 : Level} {A : UU l1} → is-set (subtype l2 A)
is-set-subtype P Q =
  is-prop-equiv
    ( extensionality-subtype P Q)
    ( is-prop-has-same-elements-subtype P Q)

subtype-Set : {l1 : Level} (l2 : Level) → UU l1 → Set (l1 ⊔ lsuc l2)
pr1 (subtype-Set l2 A) = subtype l2 A
pr2 (subtype-Set l2 A) = is-set-subtype
```
