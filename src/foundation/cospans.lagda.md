# Cospans of types

```agda
module foundation.cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A **cospan** is a pair of functions with a common codomain.

## Definition

### Cospans

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
cospan l A B =
  Σ (UU l) (λ X → (A → X) × (B → X))

module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} (c : cospan l A B)
  where

  codomain-cospan : UU l
  codomain-cospan = pr1 c

  left-map-cospan : A → codomain-cospan
  left-map-cospan = pr1 (pr2 c)

  right-map-cospan : B → codomain-cospan
  right-map-cospan = pr2 (pr2 c)
```

### Homomorphisms between cospans with fixed domains

One notion of homomorphism of cospans `c` and `d` with common domains is a map
between their codomains so that the triangles on either side commute:

```text
  A ===== A
  |       |
  v       v
  C ----> D
  ^       ^
  |       |
  B ===== B
```

```agda
module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2}
  where

  coherence-hom-codomain-cospan :
    (c d : cospan l A B) →
    (codomain-cospan c → codomain-cospan d) → UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-codomain-cospan c d h =
    ( coherence-triangle-maps (left-map-cospan d) h (left-map-cospan c)) ×
    ( coherence-triangle-maps (right-map-cospan d) h (right-map-cospan c))

  hom-codomain-cospan : (c d : cospan l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-codomain-cospan c d =
    Σ ( codomain-cospan c → codomain-cospan d)
      ( coherence-hom-codomain-cospan c d)
```

## Properties

### Characterizing equality of cospans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  htpy-cospan : (c d : cospan l A B) → UU (l1 ⊔ l2 ⊔ l)
  htpy-cospan c d =
    Σ ( codomain-cospan c ≃ codomain-cospan d)
      ( λ e → coherence-hom-codomain-cospan c d (map-equiv e))

  refl-htpy-cospan : (c : cospan l A B) → htpy-cospan c c
  pr1 (refl-htpy-cospan c) = id-equiv
  pr1 (pr2 (refl-htpy-cospan c)) = refl-htpy
  pr2 (pr2 (refl-htpy-cospan c)) = refl-htpy

  htpy-eq-cospan : (c d : cospan l A B) → c ＝ d → htpy-cospan c d
  htpy-eq-cospan c .c refl = refl-htpy-cospan c

  is-contr-total-htpy-cospan :
    (c : cospan l A B) → is-contr (Σ (cospan l A B) (htpy-cospan c))
  is-contr-total-htpy-cospan c =
    is-contr-total-Eq-structure
      ( λ X d e → coherence-hom-codomain-cospan c (X , d) (map-equiv e))
      ( is-contr-total-equiv (pr1 c))
      ( codomain-cospan c , id-equiv)
      ( is-contr-total-Eq-structure
        ( λ x f a → coherence-triangle-maps f id (right-map-cospan c))
        ( is-contr-total-htpy' (left-map-cospan c))
        ( left-map-cospan c , refl-htpy)
        (is-contr-total-htpy' (right-map-cospan c)))

  is-equiv-htpy-eq-cospan :
    (c d : cospan l A B) → is-equiv (htpy-eq-cospan c d)
  is-equiv-htpy-eq-cospan c =
    fundamental-theorem-id (is-contr-total-htpy-cospan c) (htpy-eq-cospan c)

  extensionality-cospan :
    (c d : cospan l A B) → (c ＝ d) ≃ (htpy-cospan c d)
  pr1 (extensionality-cospan c d) = htpy-eq-cospan c d
  pr2 (extensionality-cospan c d) = is-equiv-htpy-eq-cospan c d

  eq-htpy-cospan : (c d : cospan l A B) → htpy-cospan c d → c ＝ d
  eq-htpy-cospan c d = map-inv-equiv (extensionality-cospan c d)
```

## See also

- The formal dual of cospans is [spans](foundation.spans.md).
