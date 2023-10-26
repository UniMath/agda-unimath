# Equivalences of spans

```agda
module foundation.equivalences-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-spans
open import foundation.spans
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An **equivalence of (binary) spans with fixed domain and codomain** from a
[span](foundation.spans.md) `A <-f- S -g-> B` to a span `A <-h- T -k-> B`
consists of an [equivalence](foundation-core.equivalences.md) `e : S ≃ T`
[equipped with](foundation.structure.md) two homotopies `H : f ~ h ∘ e` and
`K : g ~ k ∘ e`. Equivalently, an equivalence of spans with fixed domain and
codomain is a
[morphism of spans with fixed domain and codomain](foundation.morphisms-spans.md)
of which the spanning map is an equivalence.

## Definitions

### Characterizing equality of spans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  equiv-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) → UU (l1 ⊔ l2 ⊔ l)
  equiv-span-fixed-domain-codomain c d =
    Σ ( spanning-type-span-fixed-domain-codomain c ≃
        spanning-type-span-fixed-domain-codomain d)
      ( λ e →
        coherence-hom-spanning-type-span-fixed-domain-codomain c d
          ( map-equiv e))

  id-equiv-span-fixed-domain-codomain :
    (c : span-fixed-domain-codomain l A B) →
    equiv-span-fixed-domain-codomain c c
  pr1 (id-equiv-span-fixed-domain-codomain c) = id-equiv
  pr1 (pr2 (id-equiv-span-fixed-domain-codomain c)) = refl-htpy
  pr2 (pr2 (id-equiv-span-fixed-domain-codomain c)) = refl-htpy

  htpy-eq-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) →
    c ＝ d → equiv-span-fixed-domain-codomain c d
  htpy-eq-span-fixed-domain-codomain c .c refl =
    id-equiv-span-fixed-domain-codomain c

  is-torsorial-equiv-span-fixed-domain-codomain :
    (c : span-fixed-domain-codomain l A B) →
    is-torsorial (equiv-span-fixed-domain-codomain c)
  is-torsorial-equiv-span-fixed-domain-codomain c =
    is-torsorial-Eq-structure
      ( λ X d e →
        coherence-hom-spanning-type-span-fixed-domain-codomain c
          ( X , d)
          ( map-equiv e))
      ( is-torsorial-equiv (pr1 c))
      ( spanning-type-span-fixed-domain-codomain c , id-equiv)
      ( is-torsorial-Eq-structure
        ( λ _ f a →
          coherence-triangle-maps (right-map-span-fixed-domain-codomain c) f id)
        ( is-torsorial-htpy (left-map-span-fixed-domain-codomain c))
        ( left-map-span-fixed-domain-codomain c , refl-htpy)
        (is-torsorial-htpy (right-map-span-fixed-domain-codomain c)))

  is-equiv-htpy-eq-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) →
    is-equiv (htpy-eq-span-fixed-domain-codomain c d)
  is-equiv-htpy-eq-span-fixed-domain-codomain c =
    fundamental-theorem-id
      ( is-torsorial-equiv-span-fixed-domain-codomain c)
      ( htpy-eq-span-fixed-domain-codomain c)

  extensionality-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) →
    (c ＝ d) ≃ (equiv-span-fixed-domain-codomain c d)
  pr1 (extensionality-span-fixed-domain-codomain c d) =
    htpy-eq-span-fixed-domain-codomain c d
  pr2 (extensionality-span-fixed-domain-codomain c d) =
    is-equiv-htpy-eq-span-fixed-domain-codomain c d

  eq-equiv-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) →
    equiv-span-fixed-domain-codomain c d → c ＝ d
  eq-equiv-span-fixed-domain-codomain c d =
    map-inv-equiv (extensionality-span-fixed-domain-codomain c d)
```
