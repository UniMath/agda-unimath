# Transposing biadjunctions between types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.transposing-biadjunctions-between-types
  {lI : Level} (I : Nontrivial-Bounded-Total-Order lI lI)
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
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.transposing-adjunctions-between-types I
```

</details>

## Idea

Given a map of types `q : 𝒞 → 𝒟`, we say `q` is a
{{#concept "transposing biadjoint" Disambiguation="map of types" Agda=is-transposing-biadjoint}}
if it has a transposing left and transposing right adjoint.

```text
         𝒞
     ∧   |    ∧
     |   |    |
  q! | ⊣ q* ⊣ | q∗
     |   |    |
     |   ∨    |
         𝒟
```

## Definitions

### Transposing adjoint triples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-adjoint-triple : (B → A) → (A → B) → (B → A) → UU (lI ⊔ l1 ⊔ l2)
  is-transposing-adjoint-triple q! q* q∗ =
    (is-transposing-adjunction q! q*) × (is-transposing-adjunction q* q∗)
```

### Transposing biadjoints

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-biadjoint : (A → B) → UU (lI ⊔ l1 ⊔ l2)
  is-transposing-biadjoint q* =
    (is-transposing-right-adjoint q*) × (is-transposing-left-adjoint q*)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q* : A → B}
  (H : is-transposing-biadjoint q*)
  where

  is-transposing-right-adjoint-is-transposing-biadjoint :
    is-transposing-right-adjoint q*
  is-transposing-right-adjoint-is-transposing-biadjoint =
    pr1 H

  is-transposing-left-adjoint-is-transposing-biadjoint :
    is-transposing-left-adjoint q*
  is-transposing-left-adjoint-is-transposing-biadjoint =
    pr2 H

  map-left-adjoint-is-transposing-biadjoint : B → A
  map-left-adjoint-is-transposing-biadjoint =
    pr1 is-transposing-right-adjoint-is-transposing-biadjoint

  is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint :
    is-transposing-adjunction map-left-adjoint-is-transposing-biadjoint q*
  is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint =
    pr2 is-transposing-right-adjoint-is-transposing-biadjoint

  unit-left-adjoint-is-transposing-biadjoint :
    id ⇒▵ q* ∘ map-left-adjoint-is-transposing-biadjoint
  unit-left-adjoint-is-transposing-biadjoint =
    unit-is-transposing-adjunction
      is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint

  counit-left-adjoint-is-transposing-biadjoint :
    map-left-adjoint-is-transposing-biadjoint ∘ q* ⇒▵ id
  counit-left-adjoint-is-transposing-biadjoint =
    counit-is-transposing-adjunction
      is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint

  map-right-adjoint-is-transposing-biadjoint : B → A
  map-right-adjoint-is-transposing-biadjoint =
    pr1 is-transposing-left-adjoint-is-transposing-biadjoint

  is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint :
    is-transposing-adjunction q* map-right-adjoint-is-transposing-biadjoint
  is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint =
    pr2 is-transposing-left-adjoint-is-transposing-biadjoint

  unit-right-adjoint-is-transposing-biadjoint :
    id ⇒▵ map-right-adjoint-is-transposing-biadjoint ∘ q*
  unit-right-adjoint-is-transposing-biadjoint =
    unit-is-transposing-adjunction
      is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint

  counit-right-adjoint-is-transposing-biadjoint :
    q* ∘ map-right-adjoint-is-transposing-biadjoint ⇒▵ id
  counit-right-adjoint-is-transposing-biadjoint =
    counit-is-transposing-adjunction
      is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint
```

### Transposing biadjunctions

```text
transposing-biadjunction : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
transposing-biadjunction A B = Σ (A → B) is-transposing-left-adjoint

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : transposing-adjunction A B)
  where

  map-left-adjoint-transposing-adjunction : A → B
  map-left-adjoint-transposing-adjunction = pr1 H

  is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction :
    is-transposing-left-adjoint map-left-adjoint-transposing-adjunction
  is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction = pr2 H

  map-right-adjoint-transposing-adjunction : B → A
  map-right-adjoint-transposing-adjunction =
    pr1 is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction

  is-transposing-adjunction-transposing-adjunction :
    is-transposing-adjunction
      map-left-adjoint-transposing-adjunction
      map-right-adjoint-transposing-adjunction
  is-transposing-adjunction-transposing-adjunction =
    pr2 is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction

  is-transposing-right-adjoint-map-right-adjoint-transposing-adjunction :
    is-transposing-right-adjoint map-right-adjoint-transposing-adjunction
  is-transposing-right-adjoint-map-right-adjoint-transposing-adjunction =
    ( map-left-adjoint-transposing-adjunction ,
      is-transposing-adjunction-transposing-adjunction)
```

## Properties

### The identity function is a transposing biadjoint

```agda
module _
  {l : Level} {A : UU l}
  where

  is-transposing-biadjoint-id : is-transposing-biadjoint (id {A = A})
  is-transposing-biadjoint-id =
    ( is-transposing-adjoint-id' , is-transposing-adjoint-id)
```

### Equivalences are transposing biadjoints

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  is-transposing-biadjoint-is-equiv : is-transposing-biadjoint f
  is-transposing-biadjoint-is-equiv =
    ( is-transposing-right-adjoint-is-equiv H ,
      is-transposing-left-adjoint-is-equiv H)
```

### Composition of transposing biadjoints

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-transposing-biadjoint-comp :
    {p : A → B} {q : B → C} →
    is-transposing-biadjoint q →
    is-transposing-biadjoint p →
    is-transposing-biadjoint (q ∘ p)
  is-transposing-biadjoint-comp (Q! , Q∗) (P! , P∗) =
    ( is-transposing-right-adjoint-comp Q! P! ,
      is-transposing-left-adjoint-comp Q∗ P∗)
```

### Dependent products of transposing biadjoints

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  is-transposing-biadjoint-Π :
    {q : (i : I) → A i → B i} →
    ((i : I) → is-transposing-biadjoint (q i)) →
    is-transposing-biadjoint (map-Π q)
  is-transposing-biadjoint-Π H =
    ( is-transposing-right-adjoint-Π
      ( is-transposing-right-adjoint-is-transposing-biadjoint ∘ H)) ,
    ( is-transposing-left-adjoint-Π
      ( is-transposing-left-adjoint-is-transposing-biadjoint ∘ H))
```

### Postcomposition by transposing biadjoints

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-biadjoint-postcomp :
    {l : Level} (X : UU l) {q : A → B} →
    is-transposing-biadjoint q →
    is-transposing-biadjoint (postcomp X q)
  is-transposing-biadjoint-postcomp X H =
    is-transposing-biadjoint-Π (λ _ → H)
```

### The composite transposing adjunction associated to a transposing biadjunction

Given a transposing biadjunction `q! ⊣ q* ⊣ q∗`, then we have a further
adjunction

```text
  q*q! ⊣ q*q∗.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {q* : A → B}
  (H : is-transposing-biadjoint q*)
  where

  is-transposing-adjunction-middle-comp-is-transposing-biadjoint :
    is-transposing-adjunction
      ( q* ∘ map-left-adjoint-is-transposing-biadjoint H)
      ( q* ∘ map-right-adjoint-is-transposing-biadjoint H)
  is-transposing-adjunction-middle-comp-is-transposing-biadjoint x y =
    ( is-transposing-adjoint-map-left-adjoint-is-transposing-biadjoint H
      ( x)
      ( map-right-adjoint-is-transposing-biadjoint H y)) ∘e
    ( is-transposing-adjoint-map-right-adjoint-is-transposing-biadjoint H
      ( map-left-adjoint-is-transposing-biadjoint H x)
      ( y))
```

### Retracts of transposing biadjoints are transposing biadjoints

> This remains to be formalized.

## References

{{#bibliography}}
