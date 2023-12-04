# Sequential colimits

```agda
module synthetic-homotopy-theory.sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation.equivalences
open import foundation-core.propositions
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coequalizers
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, we can construct its **standard sequential colimit** `A∞`, which is a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
satisfying the
[universal property of sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

In other words, the sequential colimit universally completes the diagram

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ ---> A∞ .
```

We often abuse notation and write `A∞` for just the codomain of the universal
cocone. You may also see the colimit written as `colimₙ Aₙ`.

## Properties

### All sequential diagrams admit a standard colimit

The standard colimit may be constructed from
[coequalizers](synthetic-homotopy-theory.coequalizers.md), because we
[have shown](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
that cocones of sequential diagrams correspond to a certain class of
[coforks](synthetic-homotopy-theory.coforks.md), and the coequalizers correspond
to sequential colimits. Since all coequalizers exist, we conclude that all
sequential colimits exist.

```agda
abstract
  standard-sequential-colimit : {l : Level} (A : sequential-diagram l) → UU l
  standard-sequential-colimit A =
    canonical-coequalizer
      ( bottom-map-cofork-cocone-sequential-diagram A)
      ( top-map-cofork-cocone-sequential-diagram A)

  cocone-standard-sequential-colimit :
    { l : Level} (A : sequential-diagram l) →
    cocone-sequential-diagram A (standard-sequential-colimit A)
  cocone-standard-sequential-colimit A =
    cocone-sequential-diagram-cofork A
      ( cofork-canonical-coequalizer
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A))

  dup-standard-sequential-colimit :
    { l : Level} {A : sequential-diagram l} →
    dependent-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
  dup-standard-sequential-colimit {A = A} =
    dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
      ( A)
      ( cocone-standard-sequential-colimit A)
      ( dup-canonical-coequalizer
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A))

  up-standard-sequential-colimit :
    { l : Level} {A : sequential-diagram l} →
    universal-property-sequential-colimit A
      (cocone-standard-sequential-colimit A)
  up-standard-sequential-colimit {A = A} =
    universal-property-dependent-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
      ( dup-standard-sequential-colimit)

module _
  { l : Level} {A : sequential-diagram l}
  where

  map-cocone-standard-sequential-colimit :
    ( n : ℕ) → family-sequential-diagram A n → standard-sequential-colimit A
  map-cocone-standard-sequential-colimit =
    map-cocone-sequential-diagram A (cocone-standard-sequential-colimit A)

  coherence-triangle-cocone-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-triangle-cocone-standard-sequential-colimit =
    coherence-triangle-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
```

### Corollaries of the universal property of sequential colimits

```agda
module _
  { l : Level} {A : sequential-diagram l}
  where

  equiv-up-standard-sequential-colimit :
    { l : Level} {X : UU l} →
    (standard-sequential-colimit A → X) ≃ (cocone-sequential-diagram A X)
  pr1 equiv-up-standard-sequential-colimit =
    cocone-map-sequential-diagram A (cocone-standard-sequential-colimit A)
  pr2 (equiv-up-standard-sequential-colimit {X = X}) =
    up-standard-sequential-colimit X

  cogap-standard-sequential-colimit :
    { l : Level} {X : UU l} →
    cocone-sequential-diagram A X → standard-sequential-colimit A → X
  cogap-standard-sequential-colimit =
    map-inv-equiv equiv-up-standard-sequential-colimit

  equiv-dup-standard-sequential-colimit :
    { l : Level} {P : standard-sequential-colimit A → UU l} →
    ( (x : standard-sequential-colimit A) → P x) ≃
    ( dependent-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
      ( P))
  pr1 equiv-dup-standard-sequential-colimit =
    dependent-cocone-map-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
      ( _)
  pr2 equiv-dup-standard-sequential-colimit =
    dup-standard-sequential-colimit _

  dependent-cogap-standard-sequential-colimit :
    { l : Level} {P : standard-sequential-colimit A → UU l} →
    dependent-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit A)
      ( P) →
    ( x : standard-sequential-colimit A) → P x
  dependent-cogap-standard-sequential-colimit =
    map-inv-equiv equiv-dup-standard-sequential-colimit
```

### The small predicate of being a sequential colimit cocone

The [proposition](foundation-core.propositions.md) `is-sequential-colimit` is
the assertion that the cogap map is an
[equivalence](foundation-core.equivalences.md). Note that this proposition is
[small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-sequential-colimits.md)
is a large proposition.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  (c : cocone-sequential-diagram A X)
  where

  is-sequential-colimit : UU (l1 ⊔ l2)
  is-sequential-colimit = is-equiv (cogap-standard-sequential-colimit c)

  is-prop-is-sequential-colimit : is-prop is-sequential-colimit
  is-prop-is-sequential-colimit =
    is-property-is-equiv (cogap-standard-sequential-colimit c)

  is-sequential-colimit-Prop : Prop (l1 ⊔ l2)
  pr1 is-sequential-colimit-Prop = is-sequential-colimit
  pr2 is-sequential-colimit-Prop = is-prop-is-sequential-colimit
```

### Homotopies between maps from the standard sequential colimit

Maps from the standard sequential colimit induce cocones under the sequential
diagrams, and a [homotopy](foundation-core.homotopies.md) between the maps is
exactly a homotopy of the cocones.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( f g : standard-sequential-colimit A → X)
  where

  htpy-out-of-standard-sequential-colimit : UU (l1 ⊔ l2)
  htpy-out-of-standard-sequential-colimit =
    htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A
        ( cocone-standard-sequential-colimit A)
        ( f))
      ( cocone-map-sequential-diagram A
        ( cocone-standard-sequential-colimit A)
        ( g))

  equiv-htpy-htpy-out-of-standard-sequential-colimit :
    htpy-out-of-standard-sequential-colimit ≃ (f ~ g)
  equiv-htpy-htpy-out-of-standard-sequential-colimit =
    ( inv-equiv equiv-dup-standard-sequential-colimit) ∘e
    ( equiv-tot
      ( λ K →
        equiv-Π-equiv-family
          ( λ n →
            equiv-Π-equiv-family
              ( λ a →
                compute-dependent-identification-eq-value-function f g
                  ( coherence-triangle-cocone-standard-sequential-colimit n a)
                  ( K n a)
                  ( K (succ-ℕ n) (map-sequential-diagram A n a))))))
```

We may then obtain a homotopy of maps from a homotopy of their induced cocones.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  { f g : standard-sequential-colimit A → X}
  ( H : htpy-out-of-standard-sequential-colimit A f g)
  where

  htpy-htpy-out-of-standard-sequential-colimit : f ~ g
  htpy-htpy-out-of-standard-sequential-colimit =
    map-equiv (equiv-htpy-htpy-out-of-standard-sequential-colimit A f g) H
```

### Thing thang

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  (c : cocone-sequential-diagram A X)
  where

  universal-property-is-sequential-colimit :
    is-sequential-colimit c → universal-property-sequential-colimit A c
  universal-property-is-sequential-colimit =
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
      ( A)
      ( cocone-standard-sequential-colimit A)
      ( c)
      ( cogap-standard-sequential-colimit c)
      ( htpy-cocone-universal-property-sequential-colimit A
        ( cocone-standard-sequential-colimit A)
        ( up-standard-sequential-colimit)
        ( c))
      ( up-standard-sequential-colimit)
```
