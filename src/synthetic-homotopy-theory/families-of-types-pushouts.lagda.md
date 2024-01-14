# The structure of a type family over a pushout

```agda
module synthetic-homotopy-theory.families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import foundation.transport-along-identifications
```

</details>

## Idea

Consider a [pushout square](synthetic-homotopy-theory.pushouts.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    V      ⌜ V
    A -----> X.
        i
```

Then the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
implies that the left map in the
[triangle](foundation-core.commuting-triangles-of-maps.md)

```text
           (X → 𝒰)
          /       \
       ≃ /         \
        ∨           ∨
  cocone s 𝒰 --> Σ (P : A → 𝒰) (Q : B → 𝒰), Π (x : S) → P (f x) ≃ Q (g x)
              ≃
```

is an [equivalence](foundation-core.equivalences.md). By the
[univalence axiom](foundation.univalence.md) it follows that the bottom map is
an equivalence. Therefore it follows that a type family over `X` is equivalently
described as the {{#concept "structure of a type family over a pushout"}}, which
consists of triples `(P , Q , e)` consisting of

```text
  P : A → 𝒰
  Q : B → 𝒰
  e : Π (x : S) → P (f x) ≃ Q (g x).
```

In other words, for any such triple `(P , Q , e)`, the type of families
`Y : X → 𝒰` equipped with
[families of equivalences](foundation.families-of-equivalences.md)

```text
  u : (a : A) → P a ≃ Y (i a)
  v : (b : B) → Q b ≃ Y (j b)
```

and a family of [homotopies](foundation-core.homotopies.md) witnessing that the
square of equivalences

```text
             u (f x)
    P (f x) --------> Y (i (f x))
      |                   |
  e x |                   | tr Y (H x)
      V                   V
    Q (g x) --------> Y (j (g x))
             v (g x)
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `x : S` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The structure of type families over span diagrams

**Note.** In the definition of structure of type families over span diagrams we will
assume that the families `A → 𝒰` and `B → 𝒰` are of the same
[universe level](foundation.universe-levels.md).

```agda
module _
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3)
  where

  structure-type-family-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  structure-type-family-pushout =
    Σ ( domain-span-diagram s → UU l)
      ( λ PA →
        Σ ( codomain-span-diagram s → UU l)
          ( λ PB →
            (x : spanning-type-span-diagram s) →
            PA (left-map-span-diagram s x) ≃ PB (right-map-span-diagram s x)))

module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  left-type-family-structure-type-family-pushout :
    domain-span-diagram s → UU l4
  left-type-family-structure-type-family-pushout = pr1 P

  right-type-family-structure-type-family-pushout :
    codomain-span-diagram s → UU l4
  right-type-family-structure-type-family-pushout = pr1 (pr2 P)

  spanning-type-family-structure-type-family-pushout :
    spanning-type-span-diagram s → UU l4
  spanning-type-family-structure-type-family-pushout =
    left-type-family-structure-type-family-pushout ∘ left-map-span-diagram s

  matching-equiv-structure-type-family-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-structure-type-family-pushout (left-map-span-diagram s x) ≃
    right-type-family-structure-type-family-pushout (right-map-span-diagram s x)
  matching-equiv-structure-type-family-pushout = pr2 (pr2 P)

  map-matching-equiv-structure-type-family-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-structure-type-family-pushout (left-map-span-diagram s x) →
    right-type-family-structure-type-family-pushout (right-map-span-diagram s x)
  map-matching-equiv-structure-type-family-pushout x =
    map-equiv (matching-equiv-structure-type-family-pushout x)
```
