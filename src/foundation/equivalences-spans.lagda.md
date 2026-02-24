# Equivalences of spans

```agda
module foundation.equivalences-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-spans
open import foundation.spans
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.operations-spans
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A {{#concept "equivalence of spans" Agda=equiv-span}} from a
[span](foundation.spans.md) `A <-f- S -g-> B` to a span `A <-h- T -k-> B`
consists of an [equivalence](foundation-core.equivalences.md) `w : S ≃ T`
[equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
             S
           / | \
        f /  |  \ h
         ∨   |   ∨
        A    |w   B
         ∧   |   ∧
        h \  |  / k
           \ ∨ /
             T
```

[commutes](foundation.commuting-triangles-of-maps.md).

## Definitions

### The predicate of being an equivalence of spans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B) (t : span l4 A B)
  where

  is-equiv-hom-span : hom-span s t → UU (l3 ⊔ l4)
  is-equiv-hom-span f = is-equiv (map-hom-span s t f)
```

### Equivalences of spans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B) (t : span l4 A B)
  where

  left-coherence-equiv-span :
    (spanning-type-span s ≃ spanning-type-span t) → UU (l1 ⊔ l3)
  left-coherence-equiv-span e =
    left-coherence-hom-span s t (map-equiv e)

  right-coherence-equiv-span :
    (spanning-type-span s ≃ spanning-type-span t) → UU (l2 ⊔ l3)
  right-coherence-equiv-span e =
    right-coherence-hom-span s t (map-equiv e)

  coherence-equiv-span :
    (spanning-type-span s ≃ spanning-type-span t) → UU (l1 ⊔ l2 ⊔ l3)
  coherence-equiv-span e = coherence-hom-span s t (map-equiv e)

  equiv-span : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-span =
    Σ ( spanning-type-span s ≃ spanning-type-span t) coherence-equiv-span

  equiv-equiv-span : equiv-span → spanning-type-span s ≃ spanning-type-span t
  equiv-equiv-span = pr1

  map-equiv-span : equiv-span → spanning-type-span s → spanning-type-span t
  map-equiv-span e = map-equiv (equiv-equiv-span e)

  left-triangle-equiv-span :
    (e : equiv-span) → left-coherence-hom-span s t (map-equiv-span e)
  left-triangle-equiv-span e = pr1 (pr2 e)

  right-triangle-equiv-span :
    (e : equiv-span) → right-coherence-hom-span s t (map-equiv-span e)
  right-triangle-equiv-span e = pr2 (pr2 e)

  hom-equiv-span : equiv-span → hom-span s t
  pr1 (hom-equiv-span e) = map-equiv-span e
  pr1 (pr2 (hom-equiv-span e)) = left-triangle-equiv-span e
  pr2 (pr2 (hom-equiv-span e)) = right-triangle-equiv-span e

  is-equiv-equiv-span :
    (e : equiv-span) → is-equiv-hom-span s t (hom-equiv-span e)
  is-equiv-equiv-span e = is-equiv-map-equiv (equiv-equiv-span e)

  compute-equiv-span :
    Σ (hom-span s t) (is-equiv-hom-span s t) ≃ equiv-span
  compute-equiv-span = equiv-right-swap-Σ
```

### The identity equivalence on a span

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  id-equiv-span : (s : span l3 A B) → equiv-span s s
  pr1 (id-equiv-span s) = id-equiv
  pr1 (pr2 (id-equiv-span s)) = refl-htpy
  pr2 (pr2 (id-equiv-span s)) = refl-htpy
```

## Properties

### Extensionality of spans

Equality of spans is equivalent to equivalences of spans.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-eq-span : (s t : span l3 A B) → s ＝ t → equiv-span s t
  equiv-eq-span s .s refl = id-equiv-span s

  abstract
    is-torsorial-equiv-span :
      (s : span l3 A B) → is-torsorial (equiv-span {l1} {l2} {l3} {l3} s)
    is-torsorial-equiv-span s =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (spanning-type-span s))
        ( spanning-type-span s , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (left-map-span s))
          ( left-map-span s , refl-htpy)
          ( is-torsorial-htpy (right-map-span s)))

  abstract
    is-equiv-equiv-eq-span : (c d : span l3 A B) → is-equiv (equiv-eq-span c d)
    is-equiv-equiv-eq-span c =
      fundamental-theorem-id (is-torsorial-equiv-span c) (equiv-eq-span c)

  extensionality-span : (c d : span l3 A B) → (c ＝ d) ≃ (equiv-span c d)
  pr1 (extensionality-span c d) = equiv-eq-span c d
  pr2 (extensionality-span c d) = is-equiv-equiv-eq-span c d

  eq-equiv-span : (c d : span l3 A B) → equiv-span c d → c ＝ d
  eq-equiv-span c d = map-inv-equiv (extensionality-span c d)
```
