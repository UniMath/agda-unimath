# Functoriality of sequential colimits

```agda
module synthetic-homotopy-theory.functoriality-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-prisms-of-maps
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.retracts-of-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Taking the
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md) is a
functorial action `(A, a) ↦ A∞`.

In other words, a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`f : (A, a) → (B, b)` induces a map `f∞ : A∞ → B∞` between the
[standard sequential colimits](synthetic-homotopy-theory.sequential-colimits.md)
of the diagrams, and this action preserves the identity morphism and morphism
composition.

Furthermore, an
[equivalence of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md)
`e : (A, a) ≃ (B, b)` induces an equivalence `e∞ : A∞ ≃ B∞`.

The development in this file is a formalization of Lemma 3.5 in Sequential
Colimits in Homotopy Type Theory.

## Properties

### A morphism of sequential diagrams induces a map of cocones

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( f : hom-sequential-diagram A B) {X : UU l3}
  where

  map-cocone-hom-sequential-diagram :
    cocone-sequential-diagram B X → cocone-sequential-diagram A X
  map-cocone-hom-sequential-diagram c =
    comp-hom-sequential-diagram A B (constant-sequential-diagram X) c f
```

### A morphism of sequential diagrams induces a map of sequential colimits

The induced map

```text
        a₀      a₁      a₂
    A₀ ---> A₁ ---> A₂ ---> ⋯ ---> A∞
    |       |       |              |
 f₀ |       | f₁    | f₂           | f∞
    V       V       V              V
    B₀ ---> B₁ ---> B₂ ---> ⋯ ---> B∞
        b₀      b₁      b₂
```

then induces a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) under
`(A, a)` with codomain `B∞`, which is homotopic to the standard cocone under
`(B, b)` precomposed by `f`.

This homotopy of cocones provides
[vertical commuting prisms of maps](foundation.commuting-prisms-of-maps.md),

```text
          Aₙ₊₁
         ^ | \
       /   |   \
     /     |fₙ₊₁ V
    Aₙ ---------> A∞
    |      |      |
    |      V      |
 fₙ |     Bₙ₊₁    | f∞
    |    ^   \    |
    |  /       \  |
    V/           VV
    Bₙ ---------> B∞ ,
```

where the [triangles](foundation-core.commuting-triangles-of-maps.md) are
coherences of the cocones of the standard sequential colimits, the back left
[square](foundation-core.commuting-triangles-of-maps.md) is coherence of `f`,
and the front and back right squares are provided by uniqueness of `f∞`.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( f : hom-sequential-diagram A B)
  where

  map-hom-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-hom-standard-sequential-colimit =
    cogap-standard-sequential-colimit
      ( map-cocone-hom-sequential-diagram f
        ( cocone-standard-sequential-colimit B))

  htpy-cocone-map-hom-standard-sequential-colimit :
    htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A
        ( cocone-standard-sequential-colimit A)
        ( map-hom-standard-sequential-colimit))
      ( map-cocone-hom-sequential-diagram f
        ( cocone-standard-sequential-colimit B))
  htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-cocone-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
      ( up-standard-sequential-colimit)
      ( map-cocone-hom-sequential-diagram f
        ( cocone-standard-sequential-colimit B))

  htpy-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-maps
      ( map-hom-sequential-diagram B f n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-hom-standard-sequential-colimit)
  htpy-htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-htpy-cocone-sequential-diagram A
      ( htpy-cocone-map-hom-standard-sequential-colimit)

  coherence-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-homotopies
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit n)
      ( ( map-hom-standard-sequential-colimit) ·l
        ( coherence-triangle-cocone-standard-sequential-colimit n))
      ( coherence-triangle-cocone-sequential-diagram A
          ( map-cocone-hom-sequential-diagram f
            ( cocone-standard-sequential-colimit B))
          ( n))
      ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
  coherence-htpy-cocone-map-hom-standard-sequential-colimit =
    coherence-htpy-htpy-cocone-sequential-diagram A
      ( htpy-cocone-map-hom-standard-sequential-colimit)

  prism-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    vertical-coherence-prism-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-hom-standard-sequential-colimit)
      ( coherence-triangle-cocone-standard-sequential-colimit n)
      ( inv-htpy (htpy-htpy-cocone-map-hom-standard-sequential-colimit n))
      ( inv-htpy
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)))
      ( naturality-map-hom-sequential-diagram B f n)
      ( coherence-triangle-cocone-standard-sequential-colimit n)
  prism-htpy-cocone-map-hom-standard-sequential-colimit n =
    rotate-vertical-coherence-prism-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-hom-standard-sequential-colimit)
      ( coherence-triangle-cocone-standard-sequential-colimit n)
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit n)
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n))
      ( naturality-map-hom-sequential-diagram B f n)
      ( coherence-triangle-cocone-standard-sequential-colimit n)
      ( inv-htpy (coherence-htpy-cocone-map-hom-standard-sequential-colimit n))
```

### Homotopies between morphisms of sequential diagrams induce homotopies of maps of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { f g : hom-sequential-diagram A B} (H : htpy-hom-sequential-diagram B f g)
  where

  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram :
    map-hom-standard-sequential-colimit B f ~
    map-hom-standard-sequential-colimit B g
  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram =
    htpy-eq
      ( ap
        ( map-hom-standard-sequential-colimit B)
        ( eq-htpy-sequential-diagram A B f g H))
```

### The identity morphism induces the identity map

We have `id∞ ~ id : A∞ → A∞`.

```agda
module _
  { l1 : Level} {A : sequential-diagram l1}
  where

  htpy-preserves-id-map-hom-standard-sequential-colimit :
    htpy-out-of-standard-sequential-colimit A
      ( map-hom-standard-sequential-colimit A
        ( id-hom-sequential-diagram A))
      ( id)
  pr1 htpy-preserves-id-map-hom-standard-sequential-colimit =
    htpy-htpy-cocone-map-hom-standard-sequential-colimit A
      ( id-hom-sequential-diagram A)
  pr2 htpy-preserves-id-map-hom-standard-sequential-colimit n =
    ( coherence-htpy-cocone-map-hom-standard-sequential-colimit A
      ( id-hom-sequential-diagram A) n) ∙h
    ( ap-concat-htpy _
      ( ( right-unit-htpy) ∙h
        ( inv-htpy
          ( left-unit-law-left-whisk-htpy
            ( coherence-triangle-cocone-standard-sequential-colimit n)))))

  preserves-id-map-hom-standard-sequential-colimit :
    map-hom-standard-sequential-colimit A
      ( id-hom-sequential-diagram A) ~
    id
  preserves-id-map-hom-standard-sequential-colimit =
    htpy-htpy-out-of-standard-sequential-colimit A
      ( htpy-preserves-id-map-hom-standard-sequential-colimit)
```

### Forming sequential colimits preserves composition of morphisms of sequential diagrams

We have `(f ∘ g)∞ ~ (f∞ ∘ g∞) : A∞ → C∞`.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { C : sequential-diagram l3}
  ( g : hom-sequential-diagram B C) (f : hom-sequential-diagram A B)
  where

  htpy-preserves-comp-map-hom-standard-sequential-colimit :
    htpy-out-of-standard-sequential-colimit A
      ( map-hom-standard-sequential-colimit C
        ( comp-hom-sequential-diagram A B C g f))
      ( ( map-hom-standard-sequential-colimit C g) ∘
        ( map-hom-standard-sequential-colimit B f))
  pr1 htpy-preserves-comp-map-hom-standard-sequential-colimit n =
    ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
      ( comp-hom-sequential-diagram A B C g f) n) ∙h
    ( pasting-vertical-coherence-square-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-standard-sequential-colimit B f)
      ( map-cocone-standard-sequential-colimit n)
      ( map-hom-sequential-diagram C g n)
      ( map-hom-standard-sequential-colimit C g)
      ( map-cocone-standard-sequential-colimit n)
      ( inv-htpy
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f n))
      ( inv-htpy
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g n)))
  pr2 htpy-preserves-comp-map-hom-standard-sequential-colimit n =
    ( inv-htpy-assoc-htpy
      ( ( map-hom-standard-sequential-colimit C
          ( comp-hom-sequential-diagram A B C g f)) ·l
        ( coherence-triangle-cocone-standard-sequential-colimit n))
      ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
          ( comp-hom-sequential-diagram A B C g f)
          ( succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( _)) ∙h
    ( ap-concat-htpy' _
      ( coherence-htpy-cocone-map-hom-standard-sequential-colimit C
        ( comp-hom-sequential-diagram A B C g f)
        ( n)) ∙h
    ( assoc-htpy
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( coherence-triangle-cocone-sequential-diagram A
        ( map-cocone-hom-sequential-diagram
          ( comp-hom-sequential-diagram A B C g f)
          ( cocone-standard-sequential-colimit C))
        ( n))
      ( _)) ∙h
    ( ap-concat-htpy
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( ( assoc-htpy
          ( ( coherence-triangle-cocone-standard-sequential-colimit n) ·r
            ( ( map-hom-sequential-diagram C g n) ∘
              ( map-hom-sequential-diagram B f n)))
          ( map-cocone-standard-sequential-colimit (succ-ℕ n) ·l _)
          ( _)) ∙h
        ( pasting-vertical-coherence-prism-maps
          ( map-cocone-standard-sequential-colimit n)
          ( map-cocone-standard-sequential-colimit (succ-ℕ n))
          ( map-sequential-diagram A n)
          ( map-cocone-standard-sequential-colimit n)
          ( map-cocone-standard-sequential-colimit (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( map-hom-sequential-diagram B f n)
          ( map-hom-sequential-diagram B f (succ-ℕ n))
          ( map-hom-standard-sequential-colimit B f)
          ( map-cocone-standard-sequential-colimit n)
          ( map-cocone-standard-sequential-colimit (succ-ℕ n))
          ( map-sequential-diagram C n)
          ( map-hom-sequential-diagram C g n)
          ( map-hom-sequential-diagram C g (succ-ℕ n))
          ( map-hom-standard-sequential-colimit C g)
          ( coherence-triangle-cocone-standard-sequential-colimit n)
          ( inv-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f n))
          ( inv-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
              ( succ-ℕ n)))
          ( naturality-map-hom-sequential-diagram B f n)
          ( coherence-triangle-cocone-standard-sequential-colimit n)
          ( inv-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g n))
          ( inv-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
              ( succ-ℕ n)))
          ( naturality-map-hom-sequential-diagram C g n)
          ( coherence-triangle-cocone-standard-sequential-colimit n)
          ( prism-htpy-cocone-map-hom-standard-sequential-colimit B f n)
          ( prism-htpy-cocone-map-hom-standard-sequential-colimit C g
            ( n))))) ∙h
    ( inv-htpy-assoc-htpy
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( _)
      ( ( ( map-hom-standard-sequential-colimit C g) ∘
          ( map-hom-standard-sequential-colimit B f)) ·l
        ( coherence-triangle-cocone-standard-sequential-colimit n))))

  preserves-comp-map-hom-standard-sequential-colimit :
    ( map-hom-standard-sequential-colimit C
      ( comp-hom-sequential-diagram A B C g f)) ~
    ( ( map-hom-standard-sequential-colimit C g) ∘
      ( map-hom-standard-sequential-colimit B f))
  preserves-comp-map-hom-standard-sequential-colimit =
    htpy-htpy-out-of-standard-sequential-colimit A
      htpy-preserves-comp-map-hom-standard-sequential-colimit
```

### An equivalence of sequential diagrams induces an equivalence of colimits

Additionally, the underlying map of the inverse equivalence is definitionally
equal to the map induced by the inverse of the equivalence of sequential
diagrams, i.e. `(e∞)⁻¹ = (e⁻¹)∞`.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( e : equiv-sequential-diagram A B)
  where

  map-equiv-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( hom-equiv-sequential-diagram B e)

  inv-map-equiv-standard-sequential-colimit :
    standard-sequential-colimit B → standard-sequential-colimit A
  inv-map-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit A
      ( hom-inv-equiv-sequential-diagram B e)

  abstract
    is-section-inv-map-equiv-standard-sequential-colimit :
      ( ( map-equiv-standard-sequential-colimit) ∘
        ( inv-map-equiv-standard-sequential-colimit)) ~
      ( id)
    is-section-inv-map-equiv-standard-sequential-colimit =
      ( inv-htpy
        ( preserves-comp-map-hom-standard-sequential-colimit
          ( hom-equiv-sequential-diagram B e)
          ( hom-inv-equiv-sequential-diagram B e))) ∙h
      ( htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram
        ( is-section-inv-equiv-sequential-diagram B e)) ∙h
      ( preserves-id-map-hom-standard-sequential-colimit)

    is-retraction-inv-map-equiv-standard-sequential-colimit :
      ( ( inv-map-equiv-standard-sequential-colimit) ∘
        ( map-equiv-standard-sequential-colimit)) ~
      ( id)
    is-retraction-inv-map-equiv-standard-sequential-colimit =
      ( inv-htpy
        ( preserves-comp-map-hom-standard-sequential-colimit
          ( hom-inv-equiv-sequential-diagram B e)
          ( hom-equiv-sequential-diagram B e))) ∙h
      ( htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram
        ( is-retraction-inv-equiv-sequential-diagram B e)) ∙h
      ( preserves-id-map-hom-standard-sequential-colimit)

  is-equiv-map-hom-standard-sequential-colimit :
    is-equiv map-equiv-standard-sequential-colimit
  is-equiv-map-hom-standard-sequential-colimit =
    is-equiv-is-invertible
      ( inv-map-equiv-standard-sequential-colimit)
      ( is-section-inv-map-equiv-standard-sequential-colimit)
      ( is-retraction-inv-map-equiv-standard-sequential-colimit)

  equiv-equiv-standard-sequential-colimit :
    standard-sequential-colimit A ≃ standard-sequential-colimit B
  pr1 equiv-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B (hom-equiv-sequential-diagram B e)
  pr2 equiv-equiv-standard-sequential-colimit =
    is-equiv-map-hom-standard-sequential-colimit
```

### A retract of sequential diagrams induces a retract of colimits

Additionally, the underlying map of the retraction is definitionally equal to
the map induced by the retraction of sequential diagrams.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( R : A retract-of-sequential-diagram B)
  where

  map-inclusion-retract-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-inclusion-retract-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( inclusion-retract-sequential-diagram A B R)

  map-hom-retraction-retract-standard-sequential-colimit :
    standard-sequential-colimit B → standard-sequential-colimit A
  map-hom-retraction-retract-standard-sequential-colimit =
    map-hom-standard-sequential-colimit A
      ( hom-retraction-retract-sequential-diagram A B R)

  abstract
    is-retraction-map-hom-retraction-retract-standard-sequential-colimit :
      is-retraction
        ( map-inclusion-retract-standard-sequential-colimit)
        ( map-hom-retraction-retract-standard-sequential-colimit)
    is-retraction-map-hom-retraction-retract-standard-sequential-colimit =
      ( inv-htpy
        ( preserves-comp-map-hom-standard-sequential-colimit
          ( hom-retraction-retract-sequential-diagram A B R)
          ( inclusion-retract-sequential-diagram A B R))) ∙h
      ( htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram
        ( is-retraction-hom-retraction-retract-sequential-diagram A B R)) ∙h
      ( preserves-id-map-hom-standard-sequential-colimit)

  retraction-retract-standard-sequential-colimit :
    retraction
      ( map-hom-standard-sequential-colimit B
        ( inclusion-retract-sequential-diagram A B R))
  pr1 retraction-retract-standard-sequential-colimit =
    map-hom-retraction-retract-standard-sequential-colimit
  pr2 retraction-retract-standard-sequential-colimit =
    is-retraction-map-hom-retraction-retract-standard-sequential-colimit

  retract-retract-standard-sequential-colimit :
    (standard-sequential-colimit A) retract-of (standard-sequential-colimit B)
  pr1 retract-retract-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( inclusion-retract-sequential-diagram A B R)
  pr2 retract-retract-standard-sequential-colimit =
    retraction-retract-standard-sequential-colimit
```

## References

1. Kristina Sojakova, Floris van Doorn, and Egbert Rijke. 2020. Sequential
   Colimits in Homotopy Type Theory. In Proceedings of the 35th Annual ACM/IEEE
   Symposium on Logic in Computer Science (LICS '20). Association for Computing
   Machinery, New York, NY, USA, 845–858,
   [DOI:10.1145](https://doi.org/10.1145/3373718.3394801)
