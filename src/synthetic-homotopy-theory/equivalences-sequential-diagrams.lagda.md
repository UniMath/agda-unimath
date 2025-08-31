# Equivalences of sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.retracts-of-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

An **equivalence of sequential diagrams** `(A, a)` and `(B, b)` is a
[sequence](lists.dependent-sequences.md) of
[equivalences](foundation.equivalences.md) `eₙ : Aₙ ≃ Bₙ` such that their
underlying maps form a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md).

Specifically, the underlying maps need to satisfy the same naturality condition.

## Definitions

### Equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  equiv-sequential-diagram : UU (l1 ⊔ l2)
  equiv-sequential-diagram =
    Σ ( ( n : ℕ) →
        family-sequential-diagram A n ≃ family-sequential-diagram B n)
      ( λ e → naturality-hom-sequential-diagram A B (map-equiv ∘ e))
```

### Components of equivalences of sequential diagrams

_Implementation note:_ As mentioned in
[`morphisms-sequential-diagrams`](synthetic-homotopy-theory.morphisms-sequential-diagrams.md),
Agda can't infer both the domain and the codomain when we use accessors for the
equivalences, and the codomain needs to be provided explicitly.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  equiv-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n ≃ family-sequential-diagram B n
  equiv-equiv-sequential-diagram = pr1 e

  map-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n → family-sequential-diagram B n
  map-equiv-sequential-diagram n = map-equiv (equiv-equiv-sequential-diagram n)

  naturality-equiv-sequential-diagram :
    naturality-hom-sequential-diagram A B map-equiv-sequential-diagram
  naturality-equiv-sequential-diagram = pr2 e

  hom-equiv-sequential-diagram : hom-sequential-diagram A B
  pr1 hom-equiv-sequential-diagram = map-equiv-sequential-diagram
  pr2 hom-equiv-sequential-diagram = naturality-equiv-sequential-diagram

  is-equiv-map-equiv-sequential-diagram :
    ( n : ℕ) →
    is-equiv (map-equiv-sequential-diagram n)
  is-equiv-map-equiv-sequential-diagram n =
    is-equiv-map-equiv (equiv-equiv-sequential-diagram n)
```

### The identity equivalence of sequential diagrams

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  id-equiv-sequential-diagram : equiv-sequential-diagram A A
  pr1 id-equiv-sequential-diagram n = id-equiv
  pr2 id-equiv-sequential-diagram n = refl-htpy
```

### Composition of equivalences of sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  where

  comp-equiv-sequential-diagram :
    equiv-sequential-diagram B C →
    equiv-sequential-diagram A B →
    equiv-sequential-diagram A C
  pr1 (comp-equiv-sequential-diagram e e') n =
    ( equiv-equiv-sequential-diagram C e n) ∘e
    ( equiv-equiv-sequential-diagram B e' n)
  pr2 (comp-equiv-sequential-diagram e e') =
    naturality-map-hom-sequential-diagram C
      ( comp-hom-sequential-diagram A B C
        ( hom-equiv-sequential-diagram C e)
        ( hom-equiv-sequential-diagram B e'))
```

### Inverses of equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  inv-equiv-sequential-diagram : equiv-sequential-diagram B A
  pr1 inv-equiv-sequential-diagram n =
    inv-equiv (equiv-equiv-sequential-diagram B e n)
  pr2 inv-equiv-sequential-diagram n =
    vertical-inv-equiv-coherence-square-maps
      ( map-sequential-diagram A n)
      ( equiv-equiv-sequential-diagram B e n)
      ( equiv-equiv-sequential-diagram B e (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( naturality-map-hom-sequential-diagram B
        ( hom-equiv-sequential-diagram B e)
        ( n))

  map-inv-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram B n → family-sequential-diagram A n
  map-inv-equiv-sequential-diagram =
    map-equiv-sequential-diagram A inv-equiv-sequential-diagram

  hom-inv-equiv-sequential-diagram : hom-sequential-diagram B A
  hom-inv-equiv-sequential-diagram =
    hom-equiv-sequential-diagram A inv-equiv-sequential-diagram
```

## Properties

### Characterization of equality of sequential diagrams

[Equality](foundation.identity-types.md) of sequential diagrams is captured by
an equivalence between them.

```agda
equiv-eq-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  A ＝ B → equiv-sequential-diagram A B
equiv-eq-sequential-diagram A .A refl = id-equiv-sequential-diagram A

abstract
  is-torsorial-equiv-sequential-diagram :
    { l1 : Level} (A : sequential-diagram l1) →
    is-torsorial (equiv-sequential-diagram {l2 = l1} A)
  is-torsorial-equiv-sequential-diagram A =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-Π
        ( λ n → is-torsorial-equiv (family-sequential-diagram A n)))
      ( family-sequential-diagram A , λ n → id-equiv)
      ( is-torsorial-Eq-Π
        ( λ n → is-torsorial-htpy' (map-sequential-diagram A n)))

  is-equiv-equiv-eq-sequential-diagram :
    { l1 : Level} (A B : sequential-diagram l1) →
    is-equiv (equiv-eq-sequential-diagram A B)
  is-equiv-equiv-eq-sequential-diagram A =
    fundamental-theorem-id
      ( is-torsorial-equiv-sequential-diagram A)
      ( equiv-eq-sequential-diagram A)

extensionality-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  ( A ＝ B) ≃ equiv-sequential-diagram A B
pr1 (extensionality-sequential-diagram A B) = equiv-eq-sequential-diagram A B
pr2 (extensionality-sequential-diagram A B) =
  is-equiv-equiv-eq-sequential-diagram A B

eq-equiv-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  equiv-sequential-diagram A B → (A ＝ B)
eq-equiv-sequential-diagram A B =
  map-inv-equiv (extensionality-sequential-diagram A B)
```

### Inverses of equivalences are inverses with respect to composition of morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  is-section-inv-equiv-sequential-diagram :
    htpy-hom-sequential-diagram B
      ( comp-hom-sequential-diagram B A B
        ( hom-equiv-sequential-diagram B e)
        ( hom-inv-equiv-sequential-diagram B e))
      ( id-hom-sequential-diagram B)
  pr1 is-section-inv-equiv-sequential-diagram n =
    is-section-map-inv-equiv (equiv-equiv-sequential-diagram B e n)
  pr2 is-section-inv-equiv-sequential-diagram n =
    inv-htpy
      ( right-inverse-law-pasting-vertical-coherence-square-maps
        ( map-sequential-diagram A n)
        ( equiv-equiv-sequential-diagram B e n)
        ( equiv-equiv-sequential-diagram B e (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( naturality-equiv-sequential-diagram B e n))

  is-retraction-inv-equiv-sequential-diagram :
    htpy-hom-sequential-diagram A
      ( comp-hom-sequential-diagram A B A
        ( hom-inv-equiv-sequential-diagram B e)
        ( hom-equiv-sequential-diagram B e))
      ( id-hom-sequential-diagram A)
  pr1 is-retraction-inv-equiv-sequential-diagram n =
    is-retraction-map-inv-equiv (equiv-equiv-sequential-diagram B e n)
  pr2 is-retraction-inv-equiv-sequential-diagram n =
    inv-htpy
      ( left-inverse-law-pasting-vertical-coherence-square-maps
        ( map-sequential-diagram A n)
        ( equiv-equiv-sequential-diagram B e n)
        ( equiv-equiv-sequential-diagram B e (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( naturality-equiv-sequential-diagram B e n))

  retraction-equiv-sequential-diagram :
    retraction-hom-sequential-diagram A B
      ( hom-equiv-sequential-diagram B e)
  pr1 retraction-equiv-sequential-diagram = hom-inv-equiv-sequential-diagram B e
  pr2 retraction-equiv-sequential-diagram =
    is-retraction-inv-equiv-sequential-diagram
```

### Equivalences of sequential diagrams induce retracts of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( e : equiv-sequential-diagram A B)
  where

  retract-equiv-sequential-diagram : retract-sequential-diagram B A
  pr1 retract-equiv-sequential-diagram = hom-equiv-sequential-diagram B e
  pr2 retract-equiv-sequential-diagram = retraction-equiv-sequential-diagram B e
```
