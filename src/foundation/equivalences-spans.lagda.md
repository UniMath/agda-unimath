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
open import foundation-core.torsorial-type-families
```

</details>

## Idea

We consider four concepts of equivalences between spans, according to our different
concepts of spans:

- Equivalences of (binary) spans with fixed domain and codomain.
- Equivalences of (binary) spans.
- Equivalences of spans of a fixed family of types.
- Equivalences of spans of families of types indexed by a fixed indexing type.

### Equivalences of binary spans with fixed domain and codomain

A **equivalence of spans with fixed domain and codomain** from a
[span](foundation.spans.md) `A <-f- S -g-> B` to a span `A <-h- T -k-> B`
consists of an [equivalence](foundation-core.equivalences.md) `w : S ≃ T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
             S
           / | \
        f /  |  \ h
         V   |   V
        A    |w   B
         ∧   |   ∧
        h \  |  / k
           \ V /
             T
```

[commutes](foundation.commuting-squares-of-maps.md).

### Equivalences of binary spans

A **equivalence of spans** from a [span](foundation.spans.md) `A <-f- S -g-> B` to
a span `C <-h- T -k-> D` consists of equivalences `u : A ≃ C`, `v : B ≃ D`, and
`w : S ≃ T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f       g
    A <----- S -----> B
    |        |        |
  u |        | w      | v
    V        V        V
    C <----- T -----> D
         h       k
```

commutes.

### Equivalences of spans of families of types

The notion of **equivalence of spans of (fixed) families of types** is the natural
generalization of the notion of equivalences of (fixed) families of types.

## Definitions

### The predicate of being an equivalence of spans with fixed domain and codomain

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span-fixed-domain-codomain l3 A B)
  (t : span-fixed-domain-codomain l4 A B)
  where

  is-equiv-hom-span-fixed-domain-codomain :
    hom-span-fixed-domain-codomain s t → UU (l3 ⊔ l4)
  is-equiv-hom-span-fixed-domain-codomain f =
    is-equiv (map-hom-span-fixed-domain-codomain s t f)
```

### Equivalences of spans with fixed domain and codomain

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span-fixed-domain-codomain l3 A B)
  (t : span-fixed-domain-codomain l4 A B)
  where

  equiv-span-fixed-domain-codomain : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-span-fixed-domain-codomain =
    Σ ( spanning-type-span-fixed-domain-codomain s ≃
        spanning-type-span-fixed-domain-codomain t)
      ( λ e → coherence-hom-span-fixed-domain-codomain s t (map-equiv e))

  equiv-equiv-span-fixed-domain-codomain :
    equiv-span-fixed-domain-codomain →
    spanning-type-span-fixed-domain-codomain s ≃
    spanning-type-span-fixed-domain-codomain t
  equiv-equiv-span-fixed-domain-codomain = pr1

  map-equiv-span-fixed-domain-codomain :
    equiv-span-fixed-domain-codomain →
    spanning-type-span-fixed-domain-codomain s →
    spanning-type-span-fixed-domain-codomain t
  map-equiv-span-fixed-domain-codomain e =
    map-equiv (equiv-equiv-span-fixed-domain-codomain e)

  left-triangle-equiv-span-fixed-domain-codomain :
    (e : equiv-span-fixed-domain-codomain) →
    left-coherence-hom-span-fixed-domain-codomain s t
      ( map-equiv-span-fixed-domain-codomain e)
  left-triangle-equiv-span-fixed-domain-codomain e =
    pr1 (pr2 e)

  right-triangle-equiv-span-fixed-domain-codomain :
    (e : equiv-span-fixed-domain-codomain) →
    right-coherence-hom-span-fixed-domain-codomain s t
      ( map-equiv-span-fixed-domain-codomain e)
  right-triangle-equiv-span-fixed-domain-codomain e =
    pr2 (pr2 e)

  hom-equiv-span-fixed-domain-codomain :
    equiv-span-fixed-domain-codomain →
    hom-span-fixed-domain-codomain s t
  pr1 (hom-equiv-span-fixed-domain-codomain e) =
    map-equiv-span-fixed-domain-codomain e
  pr1 (pr2 (hom-equiv-span-fixed-domain-codomain e)) =
    left-triangle-equiv-span-fixed-domain-codomain e
  pr2 (pr2 (hom-equiv-span-fixed-domain-codomain e)) =
    right-triangle-equiv-span-fixed-domain-codomain e

  is-equiv-equiv-span-fixed-domain-codomain :
    (e : equiv-span-fixed-domain-codomain) →
    is-equiv-hom-span-fixed-domain-codomain s t
      ( hom-equiv-span-fixed-domain-codomain e)
  is-equiv-equiv-span-fixed-domain-codomain e =
    is-equiv-map-equiv (equiv-equiv-span-fixed-domain-codomain e)

  compute-equiv-span-fixed-domain-codomain :
    Σ ( hom-span-fixed-domain-codomain s t)
      ( is-equiv-hom-span-fixed-domain-codomain s t) ≃
    equiv-span-fixed-domain-codomain
  compute-equiv-span-fixed-domain-codomain =
    equiv-right-swap-Σ
```

### The identity equivalence on a span with fixed domain and codomain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  id-equiv-span-fixed-domain-codomain :
    (c : span-fixed-domain-codomain l3 A B) →
    equiv-span-fixed-domain-codomain c c
  pr1 (id-equiv-span-fixed-domain-codomain c) = id-equiv
  pr1 (pr2 (id-equiv-span-fixed-domain-codomain c)) = refl-htpy
  pr2 (pr2 (id-equiv-span-fixed-domain-codomain c)) = refl-htpy
```

### The predicate of being an equivalence of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3) (t : span l4 l5 l6)
  where

  is-equiv-hom-span :
    (f : hom-span s t) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-hom-span f =
    is-equiv (map-domain-hom-span s t f) ×
    is-equiv (map-codomain-hom-span s t f) ×
    is-equiv (spanning-map-hom-span s t f)
```

### Equivalences of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3) (t : span l4 l5 l6)
  where

  equiv-span : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-span =
    Σ ( domain-span s ≃ domain-span t)
      ( λ e →
        Σ ( codomain-span s ≃ codomain-span t)
          ( λ f →
            equiv-span-fixed-domain-codomain
              ( extend-span-fixed-domain-codomain
                ( span-fixed-domain-codomain-span s)
                ( map-equiv e)
                ( map-equiv f))
              ( span-fixed-domain-codomain-span t)))

  module _
    (e : equiv-span)
    where

    equiv-domain-equiv-span : domain-span s ≃ domain-span t
    equiv-domain-equiv-span = pr1 e

    map-domain-equiv-span : domain-span s → domain-span t
    map-domain-equiv-span = map-equiv equiv-domain-equiv-span

    is-equiv-map-domain-equiv-span : is-equiv map-domain-equiv-span
    is-equiv-map-domain-equiv-span =
      is-equiv-map-equiv equiv-domain-equiv-span

    equiv-codomain-equiv-span : codomain-span s ≃ codomain-span t
    equiv-codomain-equiv-span = pr1 (pr2 e)

    map-codomain-equiv-span : codomain-span s → codomain-span t
    map-codomain-equiv-span = map-equiv equiv-codomain-equiv-span

    is-equiv-map-codomain-equiv-span : is-equiv map-codomain-equiv-span
    is-equiv-map-codomain-equiv-span =
      is-equiv-map-equiv equiv-codomain-equiv-span

    equiv-span-fixed-domain-codomain-equiv-span :
      equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
    equiv-span-fixed-domain-codomain-equiv-span =
      pr2 (pr2 e)

    spanning-equiv-equiv-span : spanning-type-span s ≃ spanning-type-span t
    spanning-equiv-equiv-span =
      equiv-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    spanning-map-equiv-span : spanning-type-span s → spanning-type-span t
    spanning-map-equiv-span =
      map-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    is-equiv-spanning-map-equiv-span : is-equiv spanning-map-equiv-span
    is-equiv-spanning-map-equiv-span =
      is-equiv-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    left-square-equiv-span :
      coherence-square-maps
        ( spanning-map-equiv-span)
        ( left-map-span s)
        ( left-map-span t)
        ( map-domain-equiv-span)
    left-square-equiv-span =
      left-triangle-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    right-square-equiv-span :
      coherence-square-maps
        ( spanning-map-equiv-span)
        ( right-map-span s)
        ( right-map-span t)
        ( map-codomain-equiv-span)
    right-square-equiv-span =
      right-triangle-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    hom-span-fixed-domain-codomain-equiv-span :
      hom-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
    hom-span-fixed-domain-codomain-equiv-span =
      hom-equiv-span-fixed-domain-codomain
        ( extend-span-fixed-domain-codomain
          ( span-fixed-domain-codomain-span s)
          ( map-domain-equiv-span)
          ( map-codomain-equiv-span))
        ( span-fixed-domain-codomain-span t)
        ( equiv-span-fixed-domain-codomain-equiv-span)

    hom-equiv-span : hom-span s t
    pr1 hom-equiv-span = map-domain-equiv-span
    pr1 (pr2 hom-equiv-span) = map-codomain-equiv-span
    pr2 (pr2 hom-equiv-span) = hom-span-fixed-domain-codomain-equiv-span

    is-equiv-equiv-span :
      is-equiv-hom-span s t hom-equiv-span
    pr1 is-equiv-equiv-span = is-equiv-map-domain-equiv-span
    pr1 (pr2 is-equiv-equiv-span) = is-equiv-map-codomain-equiv-span
    pr2 (pr2 is-equiv-equiv-span) = is-equiv-spanning-map-equiv-span

    compute-equiv-span :
      Σ (hom-span s t) (is-equiv-hom-span s t) ≃ equiv-span
    compute-equiv-span =
      ( equiv-tot
        ( λ e →
          ( equiv-tot
            ( λ f →
              compute-equiv-span-fixed-domain-codomain
                ( extend-span-fixed-domain-codomain
                  ( span-fixed-domain-codomain-span s)
                  ( map-equiv e)
                  ( map-equiv f))
                ( span-fixed-domain-codomain-span t))) ∘e
          ( interchange-Σ-Σ _))) ∘e
      ( interchange-Σ-Σ _)
```

## Properties

### Characterizing equality of spans with fixed domain and codomain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-eq-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l3 A B) →
    c ＝ d → equiv-span-fixed-domain-codomain c d
  equiv-eq-span-fixed-domain-codomain c .c refl =
    id-equiv-span-fixed-domain-codomain c

  is-torsorial-equiv-span-fixed-domain-codomain :
    (c : span-fixed-domain-codomain l3 A B) →
    is-torsorial (equiv-span-fixed-domain-codomain c)
  is-torsorial-equiv-span-fixed-domain-codomain c =
    is-torsorial-Eq-structure
      ( λ X d e →
        coherence-hom-span-fixed-domain-codomain c
          ( X , d)
          ( map-equiv e))
      ( is-torsorial-equiv (pr1 c))
      ( spanning-type-span-fixed-domain-codomain c , id-equiv)
      ( is-torsorial-Eq-structure
        ( λ _ f a →
          coherence-triangle-maps (right-map-span-fixed-domain-codomain c) f id)
        ( is-torsorial-htpy (left-map-span-fixed-domain-codomain c))
        ( left-map-span-fixed-domain-codomain c , refl-htpy)
        ( is-torsorial-htpy (right-map-span-fixed-domain-codomain c)))

  is-equiv-equiv-eq-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l3 A B) →
    is-equiv (equiv-eq-span-fixed-domain-codomain c d)
  is-equiv-equiv-eq-span-fixed-domain-codomain c =
    fundamental-theorem-id
      ( is-torsorial-equiv-span-fixed-domain-codomain c)
      ( equiv-eq-span-fixed-domain-codomain c)

  extensionality-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l3 A B) →
    (c ＝ d) ≃ (equiv-span-fixed-domain-codomain c d)
  pr1 (extensionality-span-fixed-domain-codomain c d) =
    equiv-eq-span-fixed-domain-codomain c d
  pr2 (extensionality-span-fixed-domain-codomain c d) =
    is-equiv-equiv-eq-span-fixed-domain-codomain c d

  eq-equiv-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l3 A B) →
    equiv-span-fixed-domain-codomain c d → c ＝ d
  eq-equiv-span-fixed-domain-codomain c d =
    map-inv-equiv (extensionality-span-fixed-domain-codomain c d)
```
