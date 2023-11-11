# Spans of types

```agda
{-# OPTIONS --cubical-compatible #-}

module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
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

  domain-span : UU l
  domain-span = pr1 c

  left-map-span : domain-span → A
  left-map-span = pr1 (pr2 c)

  right-map-span : domain-span → B
  right-map-span = pr2 (pr2 c)
```

### Homomorphisms between spans with fixed codomains

One notion of homomorphism of spans `c` and `d` with common codomains is a map
between their domains so that the triangles on either side commute:

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

  coherence-hom-domain-span :
    (c d : span l A B) → (domain-span c → domain-span d) → UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-domain-span c d h =
    ( coherence-triangle-maps (left-map-span c) (left-map-span d) h) ×
    ( coherence-triangle-maps (right-map-span c) (right-map-span d) h)

  hom-domain-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-domain-span c d =
    Σ (domain-span c → domain-span d) (coherence-hom-domain-span c d)
```

### Characterizing equality of spans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  htpy-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  htpy-span c d =
    Σ ( domain-span c ≃ domain-span d)
      ( λ e → coherence-hom-domain-span c d (map-equiv e))

  refl-htpy-span : (c : span l A B) → htpy-span c c
  pr1 (refl-htpy-span c) = id-equiv
  pr1 (pr2 (refl-htpy-span c)) = refl-htpy
  pr2 (pr2 (refl-htpy-span c)) = refl-htpy

  htpy-eq-span : (c d : span l A B) → c ＝ d → htpy-span c d
  htpy-eq-span c .c refl = refl-htpy-span c

  is-torsorial-htpy-span :
    (c : span l A B) → is-torsorial (htpy-span c)
  is-torsorial-htpy-span c =
    is-torsorial-Eq-structure
      ( λ X d e → coherence-hom-domain-span c (X , d) (map-equiv e))
      ( is-torsorial-equiv (pr1 c))
      ( domain-span c , id-equiv)
      ( is-torsorial-Eq-structure
        ( λ _ f a → coherence-triangle-maps (right-map-span c) f id)
        ( is-torsorial-htpy (left-map-span c))
        ( left-map-span c , refl-htpy)
        (is-torsorial-htpy (right-map-span c)))

  is-equiv-htpy-eq-span :
    (c d : span l A B) → is-equiv (htpy-eq-span c d)
  is-equiv-htpy-eq-span c =
    fundamental-theorem-id (is-torsorial-htpy-span c) (htpy-eq-span c)

  extensionality-span :
    (c d : span l A B) → (c ＝ d) ≃ (htpy-span c d)
  pr1 (extensionality-span c d) = htpy-eq-span c d
  pr2 (extensionality-span c d) = is-equiv-htpy-eq-span c d

  eq-htpy-span : (c d : span l A B) → htpy-span c d → c ＝ d
  eq-htpy-span c d = map-inv-equiv (extensionality-span c d)
```

### Spans are equivalent to binary relations

Using the principles of [type duality](foundation.type-duality.md) and
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md),
we can show that the type of spans `A <-- S --> B` is
[equivalent](foundation.equivalences.md) to the type of type-valued binary
relations `A → B → 𝓤`.

```agda
module _
  { l1 l2 l : Level} (A : UU l1) (B : UU l2)
  where

  equiv-span-binary-relation :
    ( A → B → UU (l1 ⊔ l2 ⊔ l)) ≃ span (l1 ⊔ l2 ⊔ l) A B
  equiv-span-binary-relation =
    ( associative-Σ (UU (l1 ⊔ l2 ⊔ l)) (λ X → X → A) (λ T → pr1 T → B)) ∘e
    ( equiv-Σ (λ T → pr1 T → B) (equiv-Pr1 (l2 ⊔ l) A) (λ P → equiv-ind-Σ)) ∘e
    ( distributive-Π-Σ) ∘e
    ( equiv-Π-equiv-family
      ( λ a → equiv-Pr1 (l1 ⊔ l) B))

  span-binary-relation :
    ( A → B → UU (l1 ⊔ l2 ⊔ l)) → span (l1 ⊔ l2 ⊔ l) A B
  pr1 (span-binary-relation R) = Σ A (λ a → Σ B (λ b → R a b))
  pr1 (pr2 (span-binary-relation R)) = pr1
  pr2 (pr2 (span-binary-relation R)) = pr1 ∘ pr2

  compute-span-binary-relation :
    map-equiv equiv-span-binary-relation ~ span-binary-relation
  compute-span-binary-relation = refl-htpy

  binary-relation-span :
    span (l1 ⊔ l2 ⊔ l) A B → (A → B → UU (l1 ⊔ l2 ⊔ l))
  binary-relation-span S a b =
    Σ ( domain-span S)
      ( λ s → (left-map-span S s ＝ a) × (right-map-span S s ＝ b))

  compute-binary-relation-span :
    map-inv-equiv equiv-span-binary-relation ~ binary-relation-span
  compute-binary-relation-span S =
    inv
      ( map-eq-transpose-equiv equiv-span-binary-relation
        ( eq-htpy-span
          ( l1 ⊔ l2 ⊔ l)
          ( A)
          ( B)
          ( _)
          ( _)
          ( ( equiv-pr1 (λ s → is-torsorial-path (left-map-span S s))) ∘e
            ( equiv-left-swap-Σ) ∘e
            ( equiv-tot
              ( λ a →
                ( equiv-tot
                  ( λ s →
                    equiv-pr1 (λ _ → is-torsorial-path (right-map-span S s)) ∘e
                    equiv-left-swap-Σ)) ∘e
                ( equiv-left-swap-Σ))) ,
            ( inv-htpy (pr1 ∘ pr2 ∘ pr2 ∘ pr2)) ,
            ( inv-htpy (pr2 ∘ pr2 ∘ pr2 ∘ pr2)))))
```

## See also

- The formal dual of spans is [cospans](foundation.cospans.md).
