# Conormed maps between types

```agda
module simplicial-type-theory.conormed-maps-between-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.equivalences
open import foundation-core.homotopies

open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-directed-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-edges-dependent-pair-types
open import simplicial-type-theory.fully-faithful-maps
open import simplicial-type-theory.horizontal-composition-natural-transformations
open import simplicial-type-theory.natural-transformations
open import simplicial-type-theory.transposing-adjunctions-between-types
open import simplicial-type-theory.transposing-biadjunctions-between-types
```

</details>

## Idea

Given a map of types `q : A → B`, that has a left and a right adjoint

```text
  q! ⊣ q ⊣ q∗
```

then we say `q` is
{{#concept "conormed" Disambiguation="map of simplicial types"}} if there's a
natural transformation

```text
  Nm_q : q∗ ⇒ q!.
```

## Definitions

### Conormed maps between types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-conormed-map : (A → B) → UU (l1 ⊔ l2)
  is-conormed-map q =
    Σ ( is-transposing-biadjoint q)
      ( λ Q →
        ( map-right-adjoint-is-transposing-biadjoint Q) ⇒▵
        ( map-left-adjoint-is-transposing-biadjoint Q))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-conormed-map q)
  where

  is-transposing-biadjoint-is-conormed-map : is-transposing-biadjoint q
  is-transposing-biadjoint-is-conormed-map = pr1 H

  is-transposing-right-adjoint-is-conormed-map :
    is-transposing-right-adjoint q
  is-transposing-right-adjoint-is-conormed-map =
    is-transposing-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  is-transposing-left-adjoint-is-conormed-map :
    is-transposing-left-adjoint q
  is-transposing-left-adjoint-is-conormed-map =
    is-transposing-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  map-left-adjoint-is-conormed-map : B → A
  map-left-adjoint-is-conormed-map =
    map-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  is-transposing-adjoint-map-left-adjoint-is-conormed-map :
    is-transposing-adjunction map-left-adjoint-is-conormed-map q
  is-transposing-adjoint-map-left-adjoint-is-conormed-map =
    is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  unit-left-adjoint-is-conormed-map :
    id ⇒▵ q ∘ map-left-adjoint-is-conormed-map
  unit-left-adjoint-is-conormed-map =
    unit-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  counit-left-adjoint-is-conormed-map :
    map-left-adjoint-is-conormed-map ∘ q ⇒▵ id
  counit-left-adjoint-is-conormed-map =
    counit-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  map-right-adjoint-is-conormed-map : B → A
  map-right-adjoint-is-conormed-map =
    map-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  is-transposing-adjoint-map-right-adjoint-is-conormed-map :
    is-transposing-adjunction q map-right-adjoint-is-conormed-map
  is-transposing-adjoint-map-right-adjoint-is-conormed-map =
    is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  unit-right-adjoint-is-conormed-map :
    id ⇒▵ map-right-adjoint-is-conormed-map ∘ q
  unit-right-adjoint-is-conormed-map =
    unit-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  counit-right-adjoint-is-conormed-map :
    q ∘ map-right-adjoint-is-conormed-map ⇒▵ id
  counit-right-adjoint-is-conormed-map =
    counit-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-conormed-map

  conorm-map-is-conormed-map :
    map-right-adjoint-is-conormed-map ⇒▵ map-left-adjoint-is-conormed-map
  conorm-map-is-conormed-map = pr2 H
```

### The wrong way unit associated to a conormed map

Given a transposing biadjoint `q! ⊣ q* ⊣ q∗` and a conorm map
`Conm_q : q∗ ⇒ q!`, we have the _wrong way unit_

```text
           η∗        Conm_q
  μ : id =====> q∗q* =====> q!q*.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B}
  (H : is-conormed-map q)
  where

  -- TODO
```

### The integral map associated to a conormed map

Here we need composition.

```agda
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-conormed-map q)
  where

  integral-map-is-conormed-map : (x y : A) → q x →₂ q y → x →₂ y
  integral-map-is-conormed-map x y f =
    map-equiv
      {! is-transposing-adjoint-map-left-adjoint-is-conormed-map H (q x) y ∘e ? !}
      {! action-simplicial-hom-simplicial-natural-transformation (conorm-map-is-conormed-map H) f  !}
      -- λ t → conorm-map-is-conormed-map H (simplicial-arrow-simplicial-hom f t) --  action-simplicial-hom-function (map-right-adjoint-is-conormed-map H) f
  -- TODO
```

### The cardinality operator associated to a conormed map

Here we need composition.

```agda
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-conormed-map q)
  where

  -- TODO
```

## Properties

### Composition of conormed maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {p : A → B} {q : B → C}
  where

  is-conormed-map-comp :
    is-conormed-map q → is-conormed-map p → is-conormed-map (q ∘ p)
  is-conormed-map-comp (Q , Conm-q) (P , Conm-p) =
    ( is-transposing-biadjoint-comp Q P) ,
    ( horizontal-comp-simplicial-natural-transformation Conm-p Conm-q)
```

## Examples

### The identity conormed map

```agda
is-conormed-map-id : {l : Level} {A : UU l} → is-conormed-map (id {A = A})
pr1 is-conormed-map-id = is-transposing-biadjoint-id
pr2 is-conormed-map-id = id-simplicial-hom
```

### Equivalences are conormed maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  is-conormed-map-is-equiv : is-conormed-map f
  pr1 is-conormed-map-is-equiv = is-transposing-biadjoint-is-equiv H
  pr2 is-conormed-map-is-equiv = id-simplicial-hom ∘ map-inv-is-equiv H
```

## References

{{#bibliography}}
