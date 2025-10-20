# Subtypes

```agda
module foundation.subtypes where

open import foundation-core.subtypes public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.univalence
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

  is-torsorial-has-same-elements-subtype :
    is-torsorial has-same-elements-subtype
  is-torsorial-has-same-elements-subtype =
    is-torsorial-Eq-Π (λ x → is-torsorial-iff (P x))

  has-same-elements-eq-subtype :
    (Q : subtype l2 A) → (P ＝ Q) → has-same-elements-subtype Q
  has-same-elements-eq-subtype .P refl =
    refl-has-same-elements-subtype

  is-equiv-has-same-elements-eq-subtype :
    (Q : subtype l2 A) → is-equiv (has-same-elements-eq-subtype Q)
  is-equiv-has-same-elements-eq-subtype =
    fundamental-theorem-id
      is-torsorial-has-same-elements-subtype
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

### Subtypes with the same elements are equivalent

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (S : subtype l2 X) (T : subtype l3 X)
  where

  equiv-has-same-elements-type-subtype :
    has-same-elements-subtype S T → type-subtype S ≃ type-subtype T
  equiv-has-same-elements-type-subtype H =
    equiv-tot (λ x → equiv-iff' (S x) (T x) (H x))
```

### A subtype `S` is equivalent to `S` precomposed with an equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (S : subtype l3 Y)
  where

  equiv-precomp-equiv-type-subtype :
    type-subtype S ≃ type-subtype (S ∘ map-equiv e)
  equiv-precomp-equiv-type-subtype =
    equiv-Σ
      ( λ x → type-Prop ((S ∘ map-equiv e) x))
      ( inv-equiv e)
      ( λ y →
        equiv-eq (ap (type-Prop ∘ S) (inv (is-section-map-inv-equiv e y))))
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
    equiv-iff-is-prop
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

### Characterization of embeddings into subtypes

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

  is-section-map-inv-emb-into-subtype :
    is-section (ind-Σ (emb-into-subtype B)) (inv-emb-into-subtype)
  is-section-map-inv-emb-into-subtype g =
    eq-type-subtype is-emb-Prop refl

  is-retraction-map-inv-emb-into-subtype :
    is-retraction (ind-Σ (emb-into-subtype B)) (inv-emb-into-subtype)
  is-retraction-map-inv-emb-into-subtype (f , b) =
    eq-type-subtype
      ( λ f → Π-Prop X (λ x → B (map-emb f x)))
      ( eq-type-subtype is-emb-Prop refl)

  equiv-emb-into-subtype :
    Σ ( X ↪ A)
      ( λ f → (x : X) → is-in-subtype B (map-emb f x)) ≃ (X ↪ type-subtype B)
  pr1 equiv-emb-into-subtype = ind-Σ (emb-into-subtype B)
  pr2 equiv-emb-into-subtype =
    is-equiv-is-invertible
      inv-emb-into-subtype
      is-section-map-inv-emb-into-subtype
      is-retraction-map-inv-emb-into-subtype
```

## See also

- [Images of subtypes](foundation.images-subtypes.md)
- [Large locale of subtypes](foundation.large-locale-of-subtypes.md)
- [Powersets](foundation.powersets.md)
- [Pullbacks of subtypes](foundation.pullbacks-subtypes.md)
