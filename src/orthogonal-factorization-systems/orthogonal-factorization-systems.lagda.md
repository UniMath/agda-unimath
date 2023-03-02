# Orthogonal factorization systems

```agda
module orthogonal-factorization-systems.orthogonal-factorization-systems where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.factorizations-of-maps
```

## Idea

An **orthogonal factorization system** is a pair of composition closed function
classes L and R containing the equivalences, such that for every function
`f : A → B` there is a unique factorization of it such that the left map is in
`L` and the right map is in `R`.

## Definition

We first define factorizations from a left and a right function class.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (L : function-class l1 l3 l4)
  (R : function-class l3 l2 l5)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-function-class-factorization-Prop : factorization f l3 → Prop (l4 ⊔ l5)
  is-function-class-factorization-Prop F =
    conj-Prop
      ( L (left-map-factorization F))
      ( R (right-map-factorization F))

  is-function-class-factorization : factorization f l3 → UU (l4 ⊔ l5)
  is-function-class-factorization =
    type-Prop ∘ is-function-class-factorization-Prop

  function-class-factorization :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  function-class-factorization =
    Σ (factorization f l3) (is-function-class-factorization)
```

### Orthogonal factorization systems

```agda
is-orthogonal-factorization-system :
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  → UU (lsuc l ⊔ lL ⊔ lR)
is-orthogonal-factorization-system {l} L R =
  ( is-composition-closed-function-class L × is-equiv-closed-function-class L) ×
  ( ( is-composition-closed-function-class R × is-equiv-closed-function-class R) ×
  ((A B : UU l) (f : A → B) → is-contr (function-class-factorization L R f)))

orthogonal-factorization-system :
  (l lL lR : Level) → UU (lsuc l ⊔ lsuc lL ⊔ lsuc lR)
orthogonal-factorization-system l lL lR =
  Σ ( function-class l l lL)
    ( λ L →
      Σ ( function-class l l lR)
        ( is-orthogonal-factorization-system L))
```

## Properties

### Being an orthogonal factorization system is a property

```agda
module _
  {l1 l2 l3 : Level}
  (L : function-class l1 l1 l2)
  (R : function-class l1 l1 l3)
  where

  is-prop-is-orthogonal-factorization-system :
    is-prop (is-orthogonal-factorization-system L R)
  is-prop-is-orthogonal-factorization-system =
    is-prop-prod
      ( is-prop-prod
        ( is-prop-is-composition-closed-function-class L)
        ( is-prop-is-equiv-closed-function-class L))
      ( is-prop-prod
        ( is-prop-prod
          ( is-prop-is-composition-closed-function-class R)
          ( is-prop-is-equiv-closed-function-class R))
        ( is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ f → is-property-is-contr))

  is-orthogonal-factorization-system-Prop : Prop (lsuc l1 ⊔ l2 ⊔ l3)
  pr1 is-orthogonal-factorization-system-Prop =
    is-orthogonal-factorization-system L R
  pr2 is-orthogonal-factorization-system-Prop =
    is-prop-is-orthogonal-factorization-system
```
