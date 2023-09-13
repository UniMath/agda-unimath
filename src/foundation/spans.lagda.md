# Spans of types

```agda
module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Idea

A **span** is a pair of functions with a common domain.

## Definition

### Spans

```agda
span :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span l A B =
  Σ (UU l) (λ X → (X → A) × (X → B))

module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} (c : span l A B)
  where

  type-span : UU l
  type-span = pr1 c

  left-map-span : type-span → A
  left-map-span = pr1 (pr2 c)

  right-map-span : type-span → B
  right-map-span = pr2 (pr2 c)
```

### Homomorphisms of cospans

One notion of homomorphism of spans `c` and `d` with common domains is a map
between their codomains so that the triangles on either side commute:

```text
  A ===== A
  ^       ^
  |       |
  C ----> D
  |       |
  v       v
  B ===== B
```

```agda
module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2}
  where

  coherence-hom-span :
    (c d : span l A B) → (type-span c → type-span d) → UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-span c d h =
    ( coherence-triangle-maps (left-map-span c) (left-map-span d) h) ×
    ( coherence-triangle-maps (right-map-span c) (right-map-span d) h)

  hom-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-span c d = Σ (type-span c → type-span d) (coherence-hom-span c d)
```

### Characterizing equality of spans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  htpy-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  htpy-span c d =
    Σ ( type-span c ≃ type-span d)
      ( λ e → coherence-hom-span c d (map-equiv e))

  refl-htpy-span : (c : span l A B) → htpy-span c c
  pr1 (refl-htpy-span c) = id-equiv
  pr1 (pr2 (refl-htpy-span c)) = refl-htpy
  pr2 (pr2 (refl-htpy-span c)) = refl-htpy

  htpy-eq-span : (c d : span l A B) → c ＝ d → htpy-span c d
  htpy-eq-span c .c refl = refl-htpy-span c

  is-contr-total-htpy-span :
    (c : span l A B) → is-contr (Σ (span l A B) (htpy-span c))
  is-contr-total-htpy-span c =
    is-contr-total-Eq-structure
      ( λ X d e → coherence-hom-span c (X , d) (map-equiv e))
      ( is-contr-total-equiv (pr1 c))
      ( type-span c , id-equiv)
      ( is-contr-total-Eq-structure
        ( λ _ f a → coherence-triangle-maps (right-map-span c) f id)
        ( is-contr-total-htpy (left-map-span c))
        ( left-map-span c , refl-htpy)
        (is-contr-total-htpy (right-map-span c)))

  is-equiv-htpy-eq-span :
    (c d : span l A B) → is-equiv (htpy-eq-span c d)
  is-equiv-htpy-eq-span c =
    fundamental-theorem-id (is-contr-total-htpy-span c) (htpy-eq-span c)

  extensionality-span :
    (c d : span l A B) → (c ＝ d) ≃ (htpy-span c d)
  pr1 (extensionality-span c d) = htpy-eq-span c d
  pr2 (extensionality-span c d) = is-equiv-htpy-eq-span c d

  eq-htpy-span : (c d : span l A B) → htpy-span c d → c ＝ d
  eq-htpy-span c d = map-inv-equiv (extensionality-span c d)
```
