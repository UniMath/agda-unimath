---
title: Set quotients
---

```agda
module foundation.set-quotients where

open import foundation-core.equivalence-relations
open import foundation.slice

open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.small-types
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

## Definitions

### Set quotients

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where
  
  set-quotient : UU (l1 ⊔ l2)
  set-quotient = small-type-Small-Type (equivalence-class-Small-Type R)

  compute-set-quotient : equivalence-class R ≃ set-quotient
  compute-set-quotient =
    equiv-is-small-type-Small-Type (equivalence-class-Small-Type R)

  set-quotient-equivalence-class : equivalence-class R → set-quotient
  set-quotient-equivalence-class = map-equiv compute-set-quotient

  equivalence-class-set-quotient : set-quotient → equivalence-class R
  equivalence-class-set-quotient = map-inv-equiv compute-set-quotient

  issec-equivalence-class-set-quotient :
    (set-quotient-equivalence-class ∘ equivalence-class-set-quotient) ~ id
  issec-equivalence-class-set-quotient =
    issec-map-inv-equiv compute-set-quotient

  isretr-equivalence-class-set-quotient :
    (equivalence-class-set-quotient ∘ set-quotient-equivalence-class) ~ id
  isretr-equivalence-class-set-quotient =
    isretr-map-inv-equiv compute-set-quotient

  emb-equivalence-class-set-quotient : set-quotient ↪ equivalence-class R
  emb-equivalence-class-set-quotient =
    emb-equiv (inv-equiv compute-set-quotient)

  emb-set-quotient-equivalence-class : equivalence-class R ↪ set-quotient
  emb-set-quotient-equivalence-class = emb-equiv compute-set-quotient

  quotient-map : A → set-quotient
  quotient-map = set-quotient-equivalence-class ∘ class R

  is-surjective-quotient-map : is-surjective quotient-map
  is-surjective-quotient-map =
    is-surjective-comp-equiv compute-set-quotient (is-surjective-class R)

  surjection-quotient-map : A ↠ set-quotient
  pr1 surjection-quotient-map = quotient-map
  pr2 surjection-quotient-map = is-surjective-quotient-map

  emb-subtype-set-quotient : set-quotient ↪ subtype l2 A
  emb-subtype-set-quotient =
    comp-emb (emb-equivalence-class R) emb-equivalence-class-set-quotient

  subtype-set-quotient : set-quotient → subtype l2 A
  subtype-set-quotient =
    subtype-equivalence-class R ∘ equivalence-class-set-quotient

  is-inhabited-subtype-set-quotient :
    (x : set-quotient) → is-inhabited-subtype (subtype-set-quotient x)
  is-inhabited-subtype-set-quotient x =
    is-inhabited-subtype-equivalence-class R (equivalence-class-set-quotient x)

  inhabited-subtype-set-quotient : set-quotient → inhabited-subtype l2 A
  inhabited-subtype-set-quotient =
    inhabited-subtype-equivalence-class R ∘ equivalence-class-set-quotient

  is-in-equivalence-class-set-quotient :
    (x : set-quotient) → A → UU l2
  is-in-equivalence-class-set-quotient x =
    is-in-equivalence-class R (equivalence-class-set-quotient x)

  is-prop-is-in-equivalence-class-set-quotient :
    (x : set-quotient) (a : A) →
    is-prop (is-in-equivalence-class-set-quotient x a)
  is-prop-is-in-equivalence-class-set-quotient x =
    is-prop-is-in-equivalence-class R (equivalence-class-set-quotient x)

  is-in-equivalence-class-set-quotient-Prop :
    (x : set-quotient) → (A → Prop l2)
  is-in-equivalence-class-set-quotient-Prop x =
    is-in-equivalence-class-Prop R (equivalence-class-set-quotient x)

  is-set-set-quotient : is-set set-quotient
  is-set-set-quotient =
    is-set-equiv'
      ( equivalence-class R)
      ( compute-set-quotient)
      ( is-set-equivalence-class R)

  quotient-Set : Set (l1 ⊔ l2)
  pr1 quotient-Set = set-quotient
  pr2 quotient-Set = is-set-set-quotient

  unit-im-set-quotient :
    hom-slice (prop-Eq-Rel R) subtype-set-quotient
  pr1 unit-im-set-quotient = quotient-map
  pr2 unit-im-set-quotient =
    ( ( subtype-equivalence-class R) ·l
      ( inv-htpy isretr-equivalence-class-set-quotient)) ·r
    ( class R)

  is-image-set-quotient :
    {l : Level} →
    is-image l (prop-Eq-Rel R) emb-subtype-set-quotient unit-im-set-quotient
  is-image-set-quotient =
    is-image-is-surjective
      ( prop-Eq-Rel R)
      ( emb-subtype-set-quotient)
      ( unit-im-set-quotient)
      ( is-surjective-quotient-map)
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-effective-quotient-map : is-effective R (quotient-map R)
  is-effective-quotient-map x y =
    equivalence-reasoning
      ( quotient-map R x ＝ quotient-map R y)
      ≃ ( equivalence-class-set-quotient R (quotient-map R x) ＝
          equivalence-class-set-quotient R (quotient-map R y))
        by equiv-ap-emb (emb-equivalence-class-set-quotient R)
      ≃ ( class R x ＝ equivalence-class-set-quotient R (quotient-map R y))
        by
        ( equiv-concat
          ( (inv ( isretr-equivalence-class-set-quotient R (class R x))))
          ( equivalence-class-set-quotient R (quotient-map R y)))
      ≃ ( class R x ＝ class R y)
        by
        ( equiv-concat'
          ( class R x)
          ( isretr-equivalence-class-set-quotient R (class R y)))
      ≃ ( sim-Eq-Rel R x y)
        by
        ( is-effective-class R x y)

  apply-effectiveness-quotient-map :
    {x y : A} → quotient-map R x ＝ quotient-map R y → sim-Eq-Rel R x y
  apply-effectiveness-quotient-map {x} {y} =
    map-equiv (is-effective-quotient-map x y)

  apply-effectiveness-quotient-map' :
    {x y : A} → sim-Eq-Rel R x y → quotient-map R x ＝ quotient-map R y
  apply-effectiveness-quotient-map' {x} {y} =
    map-inv-equiv (is-effective-quotient-map x y)

  is-surjective-and-effective-quotient-map :
    is-surjective-and-effective R (quotient-map R) -- 
  pr1 is-surjective-and-effective-quotient-map = is-surjective-quotient-map R
  pr2 is-surjective-and-effective-quotient-map = is-effective-quotient-map

  reflecting-map-quotient-map :
    reflecting-map-Eq-Rel R (set-quotient R)
  pr1 reflecting-map-quotient-map = quotient-map R
  pr2 reflecting-map-quotient-map = apply-effectiveness-quotient-map'
```

### The set quotient of `R` is a set quotient of `R`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-set-quotient-set-quotient :
    {l : Level} →
    is-set-quotient l R (quotient-Set R) (reflecting-map-quotient-map R)
  is-set-quotient-set-quotient =
    is-set-quotient-is-surjective-and-effective R
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( is-surjective-and-effective-quotient-map R)
```

### Induction into propositions on the set quotient

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  apply-dependent-universal-property-surj-quotient-map :
    {l : Level} (P : set-quotient R → Prop l) →
    ((x : A) → type-Prop (P (quotient-map R x))) →
    ((y : set-quotient R) → type-Prop (P y))
  apply-dependent-universal-property-surj-quotient-map =
    apply-dependent-universal-property-surj-is-surjective
      ( quotient-map R)
      ( is-surjective-quotient-map R)
```
