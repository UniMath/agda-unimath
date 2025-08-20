# Normed maps between types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.normed-maps-between-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
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

open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-edges-dependent-pair-types I
open import simplicial-type-theory.fully-faithful-maps I
open import simplicial-type-theory.horizontal-composition-natural-transformations I
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.transposing-adjunctions-between-types I
open import simplicial-type-theory.transposing-biadjunctions-between-types I
```

</details>

## Idea

Given a map of types `q : A → B`, that has a left and a right
[adjoint](simplicial-type-theory.transposing-adjunctions-between-types.md)

```text
  q! ⊣ q ⊣ q∗
```

then we say `q` is
{{#concept "normed" Disambiguation="map of simplicial types" Agda=is-normed-map}}
if there's a
[natural transformation](simplicial-type-theory.natural-transformations.md)

```text
  Nm_q : q! ⇒ q∗.
```

## Definitions

### Normed maps between types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-normed-map : (A → B) → UU (I1 ⊔ l1 ⊔ l2)
  is-normed-map q =
    Σ ( is-transposing-biadjoint q)
      ( λ Q →
        ( map-left-adjoint-is-transposing-biadjoint Q) ⇒▵
        ( map-right-adjoint-is-transposing-biadjoint Q))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-normed-map q)
  where

  is-transposing-biadjoint-is-normed-map : is-transposing-biadjoint q
  is-transposing-biadjoint-is-normed-map = pr1 H

  is-transposing-right-adjoint-is-normed-map :
    is-transposing-right-adjoint q
  is-transposing-right-adjoint-is-normed-map =
    is-transposing-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  is-transposing-left-adjoint-is-normed-map :
    is-transposing-left-adjoint q
  is-transposing-left-adjoint-is-normed-map =
    is-transposing-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  map-left-adjoint-is-normed-map : B → A
  map-left-adjoint-is-normed-map =
    map-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  is-transposing-adjoint-map-left-adjoint-is-normed-map :
    is-transposing-adjunction map-left-adjoint-is-normed-map q
  is-transposing-adjoint-map-left-adjoint-is-normed-map =
    is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  unit-left-adjoint-is-normed-map :
    id ⇒▵ q ∘ map-left-adjoint-is-normed-map
  unit-left-adjoint-is-normed-map =
    unit-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  counit-left-adjoint-is-normed-map :
    map-left-adjoint-is-normed-map ∘ q ⇒▵ id
  counit-left-adjoint-is-normed-map =
    counit-left-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  map-right-adjoint-is-normed-map : B → A
  map-right-adjoint-is-normed-map =
    map-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  is-transposing-adjoint-map-right-adjoint-is-normed-map :
    is-transposing-adjunction q map-right-adjoint-is-normed-map
  is-transposing-adjoint-map-right-adjoint-is-normed-map =
    is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  unit-right-adjoint-is-normed-map :
    id ⇒▵ map-right-adjoint-is-normed-map ∘ q
  unit-right-adjoint-is-normed-map =
    unit-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  counit-right-adjoint-is-normed-map :
    q ∘ map-right-adjoint-is-normed-map ⇒▵ id
  counit-right-adjoint-is-normed-map =
    counit-right-adjoint-is-transposing-biadjoint
      is-transposing-biadjoint-is-normed-map

  norm-map-is-normed-map :
    map-left-adjoint-is-normed-map ⇒▵ map-right-adjoint-is-normed-map
  norm-map-is-normed-map = pr2 H
```

### The wrong way counit associated to a normed map

Given a
[transposing biadjoint](simplicial-type-theory.transposing-biadjunctions-between-types.md)
`q! ⊣ q* ⊣ q∗`, then having a norm map `Nm_q : q! ⇒ q∗` is equivalent to having
a _wrong way counit_ map

```text
  ν : q*q! ⇒ id.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B}
  (H : is-transposing-biadjoint q)
  where

  equiv-wrong-way-counit-norm-map-is-transposing-biadjoint :
    ( q ∘ map-left-adjoint-is-transposing-biadjoint H ⇒▵ id) ≃
    ( map-left-adjoint-is-transposing-biadjoint H ⇒▵
      map-right-adjoint-is-transposing-biadjoint H)
  equiv-wrong-way-counit-norm-map-is-transposing-biadjoint =
    equiv-Π-equiv-family
    ( λ x →
      is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint H
        ( map-left-adjoint-is-transposing-biadjoint H x)
        ( x))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-normed-map q)
  where

  wrong-way-counit-is-normed-map : q ∘ map-left-adjoint-is-normed-map H ⇒▵ id
  wrong-way-counit-is-normed-map x =
    map-inv-equiv
      ( is-transposing-adjoint-map-right-adjoint-is-normed-map H
        ( map-left-adjoint-is-normed-map H x)
        ( x))
      ( norm-map-is-normed-map H x)

  wrong-way-counit-is-normed-map' :
    (x y : A) → q x →▵ q y → q (pr1 (pr1 (pr1 H)) (q x)) →▵ q y
  wrong-way-counit-is-normed-map' x y f =
    map-inv-equiv
      ( is-transposing-adjoint-map-right-adjoint-is-normed-map H
        ( map-left-adjoint-is-normed-map H (q x))
        ( q y))
      ( action-hom▵-natural-transformation▵
        ( norm-map-is-normed-map H) f)
```

### The wrong way unit associated to a normed map

Given a transposing biadjoint `q! ⊣ q* ⊣ q∗`, then having a norm map
`Nm_q : q! ⇒ q∗` is equivalent to having a _wrong way unit_ map

```text
  μ : id ⇒ q*q∗.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B}
  (H : is-transposing-biadjoint q)
  where

  equiv-wrong-way-unit-norm-map-is-transposing-biadjoint :
    ( map-left-adjoint-is-transposing-biadjoint H ⇒▵
      map-right-adjoint-is-transposing-biadjoint H) ≃
    ( id ⇒▵ q ∘ map-right-adjoint-is-transposing-biadjoint H)
  equiv-wrong-way-unit-norm-map-is-transposing-biadjoint =
    equiv-Π-equiv-family
      ( λ x →
        is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint H
          ( x)
          ( map-right-adjoint-is-transposing-biadjoint H x))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-normed-map q)
  where

  wrong-way-unit-is-normed-map : id ⇒▵ q ∘ map-right-adjoint-is-normed-map H
  wrong-way-unit-is-normed-map x =
    map-equiv
      ( is-transposing-adjoint-map-left-adjoint-is-normed-map H
        ( x)
        ( map-right-adjoint-is-normed-map H x))
      ( norm-map-is-normed-map H x)
```

### The norm map's action on edges in the image of `q`

Given a directed edge `f : q* x →▵ q* y` there is a factorization square

```text
          Nm_q(f)
   q!q* x ----> q∗q* y
     ∧             |
     |             |
     |             ∨
     x ----------> y
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-normed-map q)
  where

  action-hom-image-norm-map-is-normed-map :
    {x y : A} →
    q x →▵ q y →
    map-left-adjoint-is-normed-map H (q x) →▵
    map-right-adjoint-is-normed-map H (q y)
  action-hom-image-norm-map-is-normed-map =
    action-hom▵-natural-transformation▵ (norm-map-is-normed-map H)
```

### The factors of the cardinality of a normed map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q : A → B} (H : is-normed-map q)
  where

  factors-cardinality-is-normed-map' :
    (x : B) →
    ((q ∘ map-right-adjoint-is-normed-map H) x →▵ x) ×
    (x →▵ (q ∘ map-right-adjoint-is-normed-map H) x)
  factors-cardinality-is-normed-map' x =
    ( counit-right-adjoint-is-normed-map H x , wrong-way-unit-is-normed-map H x)
```

If `B` were Segal, we could compose these factors to obtain the cardinality.

## Properties

### Composition of normed maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {p : A → B} {q : B → C}
  where

  is-normed-map-comp :
    is-normed-map q → is-normed-map p → is-normed-map (q ∘ p)
  is-normed-map-comp (Q , Nm-q) (P , Nm-p) =
    ( is-transposing-biadjoint-comp Q P) ,
    ( horizontal-comp-natural-transformation▵ Nm-p Nm-q)
```

## Examples

### The identity normed map

```agda
is-normed-map-id : {l : Level} {A : UU l} → is-normed-map (id {A = A})
pr1 is-normed-map-id = is-transposing-biadjoint-id
pr2 is-normed-map-id = id-hom▵
```

### Equivalences are normed maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  is-normed-map-is-equiv : is-normed-map f
  pr1 is-normed-map-is-equiv = is-transposing-biadjoint-is-equiv H
  pr2 is-normed-map-is-equiv = id-hom▵ ∘ map-inv-is-equiv H
```

## References

{{#bibliography}} {{#reference CSY22}}
