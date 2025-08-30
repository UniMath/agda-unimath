# Species of types in subuniverses

```agda
module species.species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

### Idea

A {{#concept "species of types in a subuniverse" Agda=species-subuniverse}} is a
map from a [subuniverse](foundation.subuniverses.md) `P` to a subuniverse `Q`.

## Definitions

### Species of types in subuniverses

```agda
species-subuniverse :
  {l1 l2 l3 l4 : Level} → subuniverse l1 l2 → subuniverse l3 l4 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
species-subuniverse P Q = type-subuniverse P → type-subuniverse Q

species-subuniverse-domain :
  {l1 l2 : Level} (l3 : Level) → subuniverse l1 l2 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
species-subuniverse-domain l3 P = type-subuniverse P → UU l3
```

### The predicate that a species preserves cartesian products

```agda
preserves-product-species-subuniverse-domain :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2)
  (C : is-closed-under-products-subuniverse P)
  (S : species-subuniverse-domain l3 P) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
preserves-product-species-subuniverse-domain P C S =
  ( X Y : type-subuniverse P) →
  S
    ( inclusion-subuniverse P X × inclusion-subuniverse P Y ,
      C
        ( is-in-subuniverse-inclusion-subuniverse P X)
        ( is-in-subuniverse-inclusion-subuniverse P Y)) ≃
  (S X × S Y)
```

### Transport along equivalences of in species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (F : species-subuniverse P Q)
  where

  tr-species-subuniverse :
    (X Y : type-subuniverse P) →
    inclusion-subuniverse P X ≃ inclusion-subuniverse P Y →
    inclusion-subuniverse Q (F X) → inclusion-subuniverse Q (F Y)
  tr-species-subuniverse X Y e =
    tr (inclusion-subuniverse Q ∘ F) (eq-equiv-subuniverse P e)
```

### Σ-extension to species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (F : species-subuniverse P Q)
  where

  Σ-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Σ-extension-species-subuniverse X =
    Σ (is-in-subuniverse P X) (λ p → inclusion-subuniverse Q (F (X , p)))

  equiv-Σ-extension-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse Q (F X) ≃
    Σ-extension-species-subuniverse (inclusion-subuniverse P X)
  equiv-Σ-extension-species-subuniverse X =
    inv-left-unit-law-Σ-is-contr
      ( is-proof-irrelevant-is-prop
        ( is-subtype-subuniverse P (inclusion-subuniverse P X))
        ( pr2 X))
      ( pr2 X)
```

### Σ-extension to species with domain in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2)
  (F : species-subuniverse-domain l3 P)
  where

  Σ-extension-species-subuniverse-domain :
    species-types l1 (l2 ⊔ l3)
  Σ-extension-species-subuniverse-domain X =
    Σ (is-in-subuniverse P X) (λ p → (F (X , p)))

  equiv-Σ-extension-species-subuniverse-domain :
    ( X : type-subuniverse P) →
    F X ≃
    Σ-extension-species-subuniverse-domain (inclusion-subuniverse P X)
  equiv-Σ-extension-species-subuniverse-domain X =
    inv-left-unit-law-Σ-is-contr
      ( is-proof-irrelevant-is-prop
        ( is-subtype-subuniverse P (inclusion-subuniverse P X))
        ( pr2 X))
      ( pr2 X)
```

### Π-extension to species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  where

  Π-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Π-extension-species-subuniverse X =
    (p : is-in-subuniverse P X) → inclusion-subuniverse Q (S (X , p))
```
