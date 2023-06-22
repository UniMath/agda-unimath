# Functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
```

</details>

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

### Maps preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Relation l2 A) {B : UU l3} (S : Eq-Relation l4 B)
  where

  preserves-sim-Eq-Relation-Prop : (f : A → B) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-sim-Eq-Relation-Prop f =
    Π-Prop' A
      ( λ x →
        Π-Prop' A
          ( λ y →
            function-Prop
              ( sim-Eq-Relation R x y)
              ( prop-Eq-Relation S (f x) (f y))))

  preserves-sim-Eq-Relation : (f : A → B) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-sim-Eq-Relation f = type-Prop (preserves-sim-Eq-Relation-Prop f)

  is-prop-preserves-sim-Eq-Relation :
    (f : A → B) → is-prop (preserves-sim-Eq-Relation f)
  is-prop-preserves-sim-Eq-Relation f =
    is-prop-type-Prop (preserves-sim-Eq-Relation-Prop f)

  hom-Eq-Relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Eq-Relation = type-subtype preserves-sim-Eq-Relation-Prop

  map-hom-Eq-Relation : hom-Eq-Relation → A → B
  map-hom-Eq-Relation = pr1

  preserves-sim-hom-Eq-Relation :
    (f : hom-Eq-Relation) {x y : A} → sim-Eq-Relation R x y →
    sim-Eq-Relation S (map-hom-Eq-Relation f x) (map-hom-Eq-Relation f y)
  preserves-sim-hom-Eq-Relation = pr2

id-hom-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) → hom-Eq-Relation R R
pr1 (id-hom-Eq-Relation R) = id
pr2 (id-hom-Eq-Relation R) = id
```

### Equivalences preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Relation l2 A) {B : UU l3} (S : Eq-Relation l4 B)
  where

  equiv-Eq-Relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Eq-Relation =
    Σ ( A ≃ B)
      ( λ e →
        {x y : A} →
        sim-Eq-Relation R x y ↔
        sim-Eq-Relation S (map-equiv e x) (map-equiv e y))

  equiv-equiv-Eq-Relation : equiv-Eq-Relation → A ≃ B
  equiv-equiv-Eq-Relation = pr1

  map-equiv-Eq-Relation : equiv-Eq-Relation → A → B
  map-equiv-Eq-Relation e = map-equiv (equiv-equiv-Eq-Relation e)

  map-inv-equiv-Eq-Relation : equiv-Eq-Relation → B → A
  map-inv-equiv-Eq-Relation e = map-inv-equiv (equiv-equiv-Eq-Relation e)

  is-equiv-map-equiv-Eq-Relation :
    (e : equiv-Eq-Relation) → is-equiv (map-equiv-Eq-Relation e)
  is-equiv-map-equiv-Eq-Relation e =
    is-equiv-map-equiv (equiv-equiv-Eq-Relation e)

  equiv-sim-equiv-Eq-Relation :
    (e : equiv-Eq-Relation) {x y : A} →
    sim-Eq-Relation R x y ↔
    sim-Eq-Relation S (map-equiv-Eq-Relation e x) (map-equiv-Eq-Relation e y)
  equiv-sim-equiv-Eq-Relation = pr2

  preserves-sim-equiv-Eq-Relation :
    (e : equiv-Eq-Relation) {x y : A} →
    sim-Eq-Relation R x y →
    sim-Eq-Relation S (map-equiv-Eq-Relation e x) (map-equiv-Eq-Relation e y)
  preserves-sim-equiv-Eq-Relation e = pr1 (equiv-sim-equiv-Eq-Relation e)

  hom-equiv-Eq-Relation : equiv-Eq-Relation → hom-Eq-Relation R S
  pr1 (hom-equiv-Eq-Relation e) = map-equiv-Eq-Relation e
  pr2 (hom-equiv-Eq-Relation e) = preserves-sim-equiv-Eq-Relation e

id-equiv-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) → equiv-Eq-Relation R R
pr1 (id-equiv-Eq-Relation R) = id-equiv
pr1 (pr2 (id-equiv-Eq-Relation R)) = id
pr2 (pr2 (id-equiv-Eq-Relation R)) = id
```

### Maps between types satisfying the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Relation l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Relation R (type-Set QR))
  {B : UU l4} (S : Eq-Relation l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Relation S (type-Set QS))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Relation R S) →
    is-contr
      ( Σ ( type-Set QR → type-Set QS)
          ( coherence-square-maps
            ( map-hom-Eq-Relation R S h)
            ( map-reflecting-map-Eq-Relation R f)
            ( map-reflecting-map-Eq-Relation S g)))
  unique-map-is-set-quotient Uf Ug h =
    universal-property-set-quotient-is-set-quotient R QR f Uf QS
      ( pair
        ( map-reflecting-map-Eq-Relation S g ∘ map-hom-Eq-Relation R S h)
        ( λ r →
          reflects-map-reflecting-map-Eq-Relation S g
          ( preserves-sim-hom-Eq-Relation R S h r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Relation R S) →
    type-Set QR → type-Set QS
  map-is-set-quotient Uf Ug h =
    pr1 (center (unique-map-is-set-quotient Uf Ug h))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Relation R S) →
    coherence-square-maps
      ( map-hom-Eq-Relation R S h)
      ( map-reflecting-map-Eq-Relation R f)
      ( map-reflecting-map-Eq-Relation S g)
      ( map-is-set-quotient Uf Ug h)
  coherence-square-map-is-set-quotient Uf Ug h =
    pr2 (center (unique-map-is-set-quotient Uf Ug h))
```

### Functoriality of the set quotient

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Relation l2 A) {B : UU l3} (S : Eq-Relation l4 B)
  where

  unique-map-set-quotient :
    (h : hom-Eq-Relation R S) →
    is-contr
      ( Σ ( set-quotient R → set-quotient S)
          ( coherence-square-maps
            ( map-hom-Eq-Relation R S h)
            ( quotient-map R)
            ( quotient-map S)))
  unique-map-set-quotient =
    unique-map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)

  map-set-quotient :
    (h : hom-Eq-Relation R S) → set-quotient R → set-quotient S
  map-set-quotient =
    map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)

  coherence-square-map-set-quotient :
    (h : hom-Eq-Relation R S) →
    coherence-square-maps
      ( map-hom-Eq-Relation R S h)
      ( quotient-map R)
      ( quotient-map S)
      ( map-set-quotient h)
  coherence-square-map-set-quotient =
    coherence-square-map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)
```

## Properties

### Composition of reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : Eq-Relation l2 A)
  {B : UU l3} (S : Eq-Relation l4 B)
  {C : UU l5}
  where

  comp-reflecting-map-Eq-Relation :
    reflecting-map-Eq-Relation S C → hom-Eq-Relation R S →
    reflecting-map-Eq-Relation R C
  pr1 (comp-reflecting-map-Eq-Relation g f) =
    map-reflecting-map-Eq-Relation S g ∘ map-hom-Eq-Relation R S f
  pr2 (comp-reflecting-map-Eq-Relation g f) {x} {y} r =
    reflects-map-reflecting-map-Eq-Relation S g
      ( preserves-sim-hom-Eq-Relation R S f r)
```

### Characterizing equality of `hom-Eq-Relation`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Relation l2 A) {B : UU l3} (S : Eq-Relation l4 B)
  where

  htpy-hom-Eq-Relation : (f g : hom-Eq-Relation R S) → UU (l1 ⊔ l3)
  htpy-hom-Eq-Relation f g =
    map-hom-Eq-Relation R S f ~ map-hom-Eq-Relation R S g

  refl-htpy-hom-Eq-Relation :
    (f : hom-Eq-Relation R S) → htpy-hom-Eq-Relation f f
  refl-htpy-hom-Eq-Relation f = refl-htpy

  htpy-eq-hom-Eq-Relation :
    (f g : hom-Eq-Relation R S) → (f ＝ g) → htpy-hom-Eq-Relation f g
  htpy-eq-hom-Eq-Relation f .f refl = refl-htpy-hom-Eq-Relation f

  is-contr-total-htpy-hom-Eq-Relation :
    (f : hom-Eq-Relation R S) →
    is-contr (Σ (hom-Eq-Relation R S) (htpy-hom-Eq-Relation f))
  is-contr-total-htpy-hom-Eq-Relation f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-hom-Eq-Relation R S f))
      ( is-prop-preserves-sim-Eq-Relation R S)
      ( map-hom-Eq-Relation R S f)
      ( refl-htpy-hom-Eq-Relation f)
      ( preserves-sim-hom-Eq-Relation R S f)

  is-equiv-htpy-eq-hom-Eq-Relation :
    (f g : hom-Eq-Relation R S) → is-equiv (htpy-eq-hom-Eq-Relation f g)
  is-equiv-htpy-eq-hom-Eq-Relation f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-Eq-Relation f)
      ( htpy-eq-hom-Eq-Relation f)

  extensionality-hom-Eq-Relation :
    (f g : hom-Eq-Relation R S) → (f ＝ g) ≃ htpy-hom-Eq-Relation f g
  pr1 (extensionality-hom-Eq-Relation f g) = htpy-eq-hom-Eq-Relation f g
  pr2 (extensionality-hom-Eq-Relation f g) =
    is-equiv-htpy-eq-hom-Eq-Relation f g

  eq-htpy-hom-Eq-Relation :
    (f g : hom-Eq-Relation R S) → htpy-hom-Eq-Relation f g → (f ＝ g)
  eq-htpy-hom-Eq-Relation f g =
    map-inv-equiv (extensionality-hom-Eq-Relation f g)
```

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Relation l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Relation R (type-Set QR))
  {B : UU l4} (S : Eq-Relation l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Relation S (type-Set QS))
  where

  unique-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Relation R S) →
    is-contr
      ( Σ ( type-Set QR ≃ type-Set QS)
          ( λ h' →
            coherence-square-maps
              ( map-equiv-Eq-Relation R S h)
              ( map-reflecting-map-Eq-Relation R f)
              ( map-reflecting-map-Eq-Relation S g)
              ( map-equiv h')))
  unique-equiv-is-set-quotient Uf Ug h =
    uniqueness-set-quotient R QR f Uf QS
      ( comp-reflecting-map-Eq-Relation R S g (hom-equiv-Eq-Relation R S h))
      ( is-set-quotient-is-surjective-and-effective R QS
        ( comp-reflecting-map-Eq-Relation R S g (hom-equiv-Eq-Relation R S h))
        ( ( is-surjective-comp
            ( is-surjective-is-set-quotient S QS g Ug)
            ( is-surjective-is-equiv (is-equiv-map-equiv-Eq-Relation R S h))) ,
          ( λ x y →
            ( inv-equiv
              ( equiv-iff'
                ( prop-Eq-Relation R x y)
                ( prop-Eq-Relation S
                  ( map-equiv-Eq-Relation R S h x)
                  ( map-equiv-Eq-Relation R S h y))
                ( equiv-sim-equiv-Eq-Relation R S h))) ∘e
            ( is-effective-is-set-quotient S QS g Ug
              ( map-equiv-Eq-Relation R S h x)
              ( map-equiv-Eq-Relation R S h y)))))

  equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Relation R S) → type-Set QR ≃ type-Set QS
  equiv-is-set-quotient Uf Ug h =
    pr1 (center (unique-equiv-is-set-quotient Uf Ug h))

  coherence-square-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Relation R S) →
    coherence-square-maps (map-equiv-Eq-Relation R S h)
      ( map-reflecting-map-Eq-Relation R f)
      ( map-reflecting-map-Eq-Relation S g)
      ( map-equiv (equiv-is-set-quotient Uf Ug h))
  coherence-square-equiv-is-set-quotient Uf Ug h =
    pr2 (center (unique-equiv-is-set-quotient Uf Ug h))
```

### Functoriality of set quotients preserves identity maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : Eq-Relation l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Relation R (type-Set QR))
  where

  id-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    map-is-set-quotient R QR f R QR f Uf Uf (id-hom-Eq-Relation R) ~ id
  id-map-is-set-quotient Uf x =
    ap
      ( λ c → pr1 c x)
      { x =
        center
          ( unique-map-is-set-quotient
              R QR f R QR f Uf Uf (id-hom-Eq-Relation R))}
      { y = pair id refl-htpy}
      ( eq-is-contr
        ( unique-map-is-set-quotient
            R QR f R QR f Uf Uf (id-hom-Eq-Relation R)))

  id-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    htpy-equiv
      ( equiv-is-set-quotient R QR f R QR f Uf Uf (id-equiv-Eq-Relation R))
      ( id-equiv)
  id-equiv-is-set-quotient Uf x =
    ap
      ( λ c → map-equiv (pr1 c) x)
      { x =
        center
          ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf
            ( id-equiv-Eq-Relation R))}
      { y = pair id-equiv refl-htpy}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf
          ( id-equiv-Eq-Relation R)))
```
