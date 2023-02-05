---
title: Exponents of set quotients
---

```agda
module foundation.exponents-set-quotients where

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.functoriality-set-quotients
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

## Idea

Given a type `A` equipped with an equivalence relation `R` and a type `B` equipped with an equivalence relation `S`, the type `A/R → B/S` is equivalent to the set quotient

```md
  (map-Eq-Rel R S) / ~
```

where `f ~ g := (x : A) → S (f x) (g x)`.

## Definitions

### Equivalence relation on relation preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  rel-map-Eq-Rel : Rel-Prop (l1 ⊔ l4) (map-Eq-Rel R S)
  rel-map-Eq-Rel f g =
    Π-Prop
      ( A)
      ( λ x → prop-Eq-Rel S (map-map-Eq-Rel R S f x) (map-map-Eq-Rel R S g x))

  sim-map-Eq-Rel : (f g : map-Eq-Rel R S) → UU (l1 ⊔ l4)
  sim-map-Eq-Rel = type-Rel-Prop (rel-map-Eq-Rel)

  refl-sim-map-Eq-Rel :
    (f : map-Eq-Rel R S) → sim-map-Eq-Rel f f
  refl-sim-map-Eq-Rel f x = refl-Eq-Rel S

  symm-sim-map-Eq-Rel :
    (f g : map-Eq-Rel R S) → sim-map-Eq-Rel f g → sim-map-Eq-Rel g f
  symm-sim-map-Eq-Rel f g r x = symm-Eq-Rel S (r x)

  trans-sim-map-Eq-Rel :
    (f g h : map-Eq-Rel R S) →
    sim-map-Eq-Rel f g → sim-map-Eq-Rel g h → sim-map-Eq-Rel f h
  trans-sim-map-Eq-Rel f g h r s x = trans-Eq-Rel S (r x) (s x)

  eq-rel-map-Eq-Rel :
    Eq-Rel (l1 ⊔ l4) (map-Eq-Rel R S)
  pr1 eq-rel-map-Eq-Rel = rel-map-Eq-Rel
  pr1 (pr2 eq-rel-map-Eq-Rel) {f} = refl-sim-map-Eq-Rel f
  pr1 (pr2 (pr2 eq-rel-map-Eq-Rel)) {f} {g} = symm-sim-map-Eq-Rel f g
  pr2 (pr2 (pr2 eq-rel-map-Eq-Rel)) {f} {g} {h} = trans-sim-map-Eq-Rel f g h
```

### The quotient map of `sim-map-Eq-Rel`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (qR : reflecting-map-Eq-Rel R (type-Set QR))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (qS : reflecting-map-Eq-Rel S (type-Set QS))
  (UqS : {l : Level} → is-set-quotient l S QS qS)
  where

  quotient-set-sim-map-Eq-Rel : Set (l3 ⊔ l6)
  quotient-set-sim-map-Eq-Rel = hom-Set QR QS

  type-quotient-set-sim-map-Eq-Rel : UU (l3 ⊔ l6)
  type-quotient-set-sim-map-Eq-Rel = type-Set quotient-set-sim-map-Eq-Rel

  quotient-map-sim-map-Eq-Rel :
    map-Eq-Rel R S → type-quotient-set-sim-map-Eq-Rel
  quotient-map-sim-map-Eq-Rel = map-is-set-quotient R QR qR S QS qS UqR UqS
```
