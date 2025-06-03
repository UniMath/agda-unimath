# Factorizations of maps into function classes

```agda
module orthogonal-factorization-systems.factorizations-of-maps-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.global-function-classes
```

</details>

## Idea

A **function class factorization** of a map `f : A → B` into
[function classes](orthogonal-factorization-systems.function-classes.md) `L` and
`R` is a pair of maps `l : A → X` and `r : X → B`, where `l ∈ L` and `r ∈ R`,
such that their composite `r ∘ l` is `f`.

```text
         X
        ∧ \
 L ∋ l /   \ r ∈ R
      /     ∨
    A -----> B
        f
```

## Definitions

### The predicate of being a function class factorization

```agda
module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  {A : UU l1} {B : UU l2} {f : A → B}
  (F : factorization l3 f)
  where

  is-function-class-factorization-Prop : Prop (lL ⊔ lR)
  is-function-class-factorization-Prop =
    product-Prop
      ( L (left-map-factorization F))
      ( R (right-map-factorization F))

  is-function-class-factorization : UU (lL ⊔ lR)
  is-function-class-factorization =
    type-Prop is-function-class-factorization-Prop

  is-prop-is-function-class-factorization :
    is-prop is-function-class-factorization
  is-prop-is-function-class-factorization =
    is-prop-type-Prop is-function-class-factorization-Prop

  is-in-left-class-left-map-is-function-class-factorization :
    is-function-class-factorization →
    is-in-function-class L (left-map-factorization F)
  is-in-left-class-left-map-is-function-class-factorization = pr1

  is-in-right-class-right-map-is-function-class-factorization :
    is-function-class-factorization →
    is-in-function-class R (right-map-factorization F)
  is-in-right-class-right-map-is-function-class-factorization = pr2

  left-class-map-is-function-class-factorization :
    is-function-class-factorization →
    type-function-class L A (image-factorization F)
  pr1 (left-class-map-is-function-class-factorization x) =
    left-map-factorization F
  pr2 (left-class-map-is-function-class-factorization x) =
    is-in-left-class-left-map-is-function-class-factorization x

  right-class-map-is-function-class-factorization :
    is-function-class-factorization →
    type-function-class R (image-factorization F) B
  pr1 (right-class-map-is-function-class-factorization x) =
    right-map-factorization F
  pr2 (right-class-map-is-function-class-factorization x) =
    is-in-right-class-right-map-is-function-class-factorization x
```

### The type of factorizations into function classes

```agda
function-class-factorization :
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
function-class-factorization {l3 = l3} L R f =
  Σ (factorization l3 f) (is-function-class-factorization L R)

module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  {A : UU l1} {B : UU l2} {f : A → B}
  (F : function-class-factorization L R f)
  where

  factorization-function-class-factorization : factorization l3 f
  factorization-function-class-factorization = pr1 F

  is-function-class-factorization-function-class-factorization :
    is-function-class-factorization L R
      ( factorization-function-class-factorization)
  is-function-class-factorization-function-class-factorization = pr2 F

  image-function-class-factorization : UU l3
  image-function-class-factorization =
    image-factorization factorization-function-class-factorization

  left-map-function-class-factorization :
    A → image-function-class-factorization
  left-map-function-class-factorization =
    left-map-factorization factorization-function-class-factorization

  right-map-function-class-factorization :
    image-function-class-factorization → B
  right-map-function-class-factorization =
    right-map-factorization factorization-function-class-factorization

  is-factorization-function-class-factorization :
    is-factorization f
      ( right-map-function-class-factorization)
      ( left-map-function-class-factorization)
  is-factorization-function-class-factorization =
    is-factorization-factorization factorization-function-class-factorization

  is-in-left-class-left-map-function-class-factorization :
    is-in-function-class L left-map-function-class-factorization
  is-in-left-class-left-map-function-class-factorization =
    is-in-left-class-left-map-is-function-class-factorization L R
      ( factorization-function-class-factorization)
      ( is-function-class-factorization-function-class-factorization)

  is-in-right-class-right-map-function-class-factorization :
    is-in-function-class R right-map-function-class-factorization
  is-in-right-class-right-map-function-class-factorization =
    is-in-right-class-right-map-is-function-class-factorization L R
      ( factorization-function-class-factorization)
      ( is-function-class-factorization-function-class-factorization)

  left-class-map-function-class-factorization :
    type-function-class L A image-function-class-factorization
  left-class-map-function-class-factorization =
    left-class-map-is-function-class-factorization L R
      ( factorization-function-class-factorization)
      ( is-function-class-factorization-function-class-factorization)

  right-class-map-function-class-factorization :
    type-function-class R image-function-class-factorization B
  right-class-map-function-class-factorization =
    right-class-map-is-function-class-factorization L R
      ( factorization-function-class-factorization)
      ( is-function-class-factorization-function-class-factorization)
```

## Properties

### Characterization of identifications of factorizations of a map into function classes

**Proof:** This follows immediately from the characterization of identifications
of factorizations using the
[subtype identity principle](foundation.subtype-identity-principle.md).

What follows is a long list of auxiliary definitions.

```agda
module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  equiv-function-class-factorization :
    (F E : function-class-factorization L R f) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-function-class-factorization F E =
    equiv-factorization f
      ( factorization-function-class-factorization L R F)
      ( factorization-function-class-factorization L R E)

  id-equiv-function-class-factorization :
    (F : function-class-factorization L R f) →
    equiv-function-class-factorization F F
  id-equiv-function-class-factorization F =
    id-equiv-factorization f
      ( factorization-function-class-factorization L R F)

  equiv-eq-function-class-factorization :
    (F E : function-class-factorization L R f) →
    F ＝ E → equiv-function-class-factorization F E
  equiv-eq-function-class-factorization F E p =
    equiv-eq-factorization f
      ( factorization-function-class-factorization L R F)
      ( factorization-function-class-factorization L R E)
      ( ap pr1 p)

  is-torsorial-equiv-function-class-factorization :
    (F : function-class-factorization L R f) →
    is-torsorial (equiv-function-class-factorization F)
  is-torsorial-equiv-function-class-factorization F =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv-factorization f
        ( factorization-function-class-factorization L R F))
      ( is-prop-is-function-class-factorization L R)
      ( factorization-function-class-factorization L R F)
      ( id-equiv-function-class-factorization F)
      ( is-function-class-factorization-function-class-factorization L R F)

  is-equiv-equiv-eq-function-class-factorization :
    (F E : function-class-factorization L R f) →
    is-equiv (equiv-eq-function-class-factorization F E)
  is-equiv-equiv-eq-function-class-factorization F =
    fundamental-theorem-id
      ( is-torsorial-equiv-function-class-factorization F)
      ( equiv-eq-function-class-factorization F)

  extensionality-function-class-factorization :
    (F E : function-class-factorization L R f) →
    (F ＝ E) ≃ (equiv-function-class-factorization F E)
  pr1 (extensionality-function-class-factorization F E) =
    equiv-eq-function-class-factorization F E
  pr2 (extensionality-function-class-factorization F E) =
    is-equiv-equiv-eq-function-class-factorization F E

  eq-equiv-function-class-factorization :
    (F E : function-class-factorization L R f) →
    equiv-function-class-factorization F E → F ＝ E
  eq-equiv-function-class-factorization F E =
    map-inv-equiv (extensionality-function-class-factorization F E)
```

## See also

- [Factorizations of maps into global function classes](orthogonal-factorization-systems.factorizations-of-maps-global-function-classes.md)
  for the universe polymorphic version.
