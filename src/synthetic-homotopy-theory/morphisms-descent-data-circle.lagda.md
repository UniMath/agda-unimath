# Morphisms of descent data of the circle

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.morphisms-descent-data-circle
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext univalence
open import foundation.universe-levels

open import structured-types.morphisms-types-equipped-with-automorphisms funext univalence truncations

open import synthetic-homotopy-theory.descent-circle funext univalence truncations
```

</details>

## Idea

Given two [descent data](synthetic-homotopy-theory.descent-circle.md) `(A,e)`
and `(B,f)` over the
[circle](synthetic-homotopy-theory.circle.md)`, a **morphism** `h`of descent data between`(A,
e)`and`(B, f)`is a map`h`from`A`to`B` such that the square

```text
      h
  A -----> B
  |        |
 e|        |f
  ∨        ∨
  A -----> B
      h
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

### Morphisms of descent data for the circle

```agda
hom-descent-data-circle :
  { l1 l2 : Level}
  ( P : descent-data-circle l1) (Q : descent-data-circle l2) →
  UU (l1 ⊔ l2)
hom-descent-data-circle = hom-Type-With-Automorphism

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( h : hom-descent-data-circle P Q)
  where

  map-hom-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-hom-descent-data-circle =
    map-hom-Type-With-Automorphism P Q h

  coherence-square-hom-descent-data-circle :
    coherence-square-maps
      ( map-hom-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-hom-descent-data-circle)
  coherence-square-hom-descent-data-circle =
    coherence-square-hom-Type-With-Automorphism P Q h
```
