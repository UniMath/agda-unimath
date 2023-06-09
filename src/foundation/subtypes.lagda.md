# Subtypes

<details><summary>Imports</summary>
```agda
module foundation.subtypes where
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes public
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-function-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
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

  refl-has-same-elements-subtype : has-same-elements-subtype P
  pr1 (refl-has-same-elements-subtype x) = id
  pr2 (refl-has-same-elements-subtype x) = id

  is-contr-total-has-same-elements-subtype :
    is-contr (Σ (subtype l2 A) has-same-elements-subtype)
  is-contr-total-has-same-elements-subtype =
    is-contr-total-Eq-Π
      ( λ x Q → P x ⇔ Q)
      ( λ x → is-contr-total-iff (P x))

  extensionality-subtype :
    (Q : subtype l2 A) → (P ＝ Q) ≃ has-same-elements-subtype Q
  extensionality-subtype =
    extensionality-Π P
      ( λ x Q → P x ⇔ Q)
      ( λ x Q → propositional-extensionality (P x) Q)

  has-same-elements-eq-subtype :
    (Q : subtype l2 A) → (P ＝ Q) → has-same-elements-subtype Q
  has-same-elements-eq-subtype Q = map-equiv (extensionality-subtype Q)

  eq-has-same-elements-subtype :
    (Q : subtype l2 A) → has-same-elements-subtype Q → P ＝ Q
  eq-has-same-elements-subtype Q = map-inv-equiv (extensionality-subtype Q)

  refl-extensionality-subtype :
    map-equiv (extensionality-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-subtype = refl
```

### The type of all subtypes of a type is a set

```agda
is-set-subtype :
  {l1 l2 : Level} {A : UU l1} → is-set (subtype l2 A)
is-set-subtype {l1} {l2} {A} P Q =
  is-prop-equiv
    ( extensionality-subtype P Q)
    ( is-prop-Π (λ x → is-prop-iff-Prop (P x) (Q x)))

subtype-Set : {l1 : Level} (l2 : Level) → UU l1 → Set (l1 ⊔ lsuc l2)
pr1 (subtype-Set {l1} l2 A) = subtype l2 A
pr2 (subtype-Set {l1} l2 A) = is-set-subtype
```

### Characterisation of embeddings into subtypes

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : subtype l2 A) {X : UU l3}
  where

  inv-emb-into-subtype :
    (g : X ↪ type-subtype B) →
    Σ (X ↪ A) (λ f → (x : X) → is-in-subtype B (map-emb f x))
  pr1 (pr1 (inv-emb-into-subtype g)) =
    inclusion-subtype B ∘ map-emb g
  pr2 (pr1 (inv-emb-into-subtype g)) =
    is-emb-comp _ _ (is-emb-inclusion-subtype B) (is-emb-map-emb g)
  pr2 (inv-emb-into-subtype g) x =
    pr2 (map-emb g x)

  issec-map-inv-emb-into-subtype :
    ( ind-Σ (emb-into-subtype B) ∘ inv-emb-into-subtype) ~ id
  issec-map-inv-emb-into-subtype g =
    eq-type-subtype
      is-emb-Prop
      refl

  isretr-map-inv-emb-into-subtype :
    ( inv-emb-into-subtype ∘ ind-Σ (emb-into-subtype B)) ~ id
  isretr-map-inv-emb-into-subtype (f , b) =
    eq-type-subtype
      (λ f → Π-Prop X (λ x → B (map-emb f x)))
      (eq-type-subtype
        is-emb-Prop
        refl)

  equiv-emb-into-subtype :
    Σ (X ↪ A) (λ f → (x : X) → is-in-subtype B (map-emb f x)) ≃ (X ↪ type-subtype B)
  pr1 equiv-emb-into-subtype = ind-Σ (emb-into-subtype B)
  pr2 equiv-emb-into-subtype =
    is-equiv-has-inverse
      inv-emb-into-subtype
      issec-map-inv-emb-into-subtype
      isretr-map-inv-emb-into-subtype
```

