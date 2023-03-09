# Functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

</details>

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

### Maps preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  preserves-sim-Eq-Rel-Prop : (f : A → B) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-sim-Eq-Rel-Prop f =
    Π-Prop' A
      ( λ x →
        Π-Prop' A
          ( λ y →
            function-Prop (sim-Eq-Rel R x y) (prop-Eq-Rel S (f x) (f y))))

  preserves-sim-Eq-Rel : (f : A → B) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-sim-Eq-Rel f = type-Prop (preserves-sim-Eq-Rel-Prop f)

  is-prop-preserves-sim-Eq-Rel :
    (f : A → B) → is-prop (preserves-sim-Eq-Rel f)
  is-prop-preserves-sim-Eq-Rel f =
    is-prop-type-Prop (preserves-sim-Eq-Rel-Prop f)

  hom-Eq-Rel : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Eq-Rel = type-subtype preserves-sim-Eq-Rel-Prop

  map-hom-Eq-Rel : hom-Eq-Rel → A → B
  map-hom-Eq-Rel = pr1

  preserves-sim-hom-Eq-Rel :
    (f : hom-Eq-Rel) {x y : A} → sim-Eq-Rel R x y →
    sim-Eq-Rel S (map-hom-Eq-Rel f x) (map-hom-Eq-Rel f y)
  preserves-sim-hom-Eq-Rel = pr2

id-hom-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → hom-Eq-Rel R R
pr1 (id-hom-Eq-Rel R) = id
pr2 (id-hom-Eq-Rel R) = id
```

### Equivalences preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  equiv-Eq-Rel : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Eq-Rel =
    Σ ( A ≃ B)
      ( λ e →
        {x y : A} →
        sim-Eq-Rel R x y ↔ sim-Eq-Rel S (map-equiv e x) (map-equiv e y))

  equiv-equiv-Eq-Rel : equiv-Eq-Rel → A ≃ B
  equiv-equiv-Eq-Rel = pr1

  map-equiv-Eq-Rel : equiv-Eq-Rel → A → B
  map-equiv-Eq-Rel e = map-equiv (equiv-equiv-Eq-Rel e)

  map-inv-equiv-Eq-Rel : equiv-Eq-Rel → B → A
  map-inv-equiv-Eq-Rel e = map-inv-equiv (equiv-equiv-Eq-Rel e)

  is-equiv-map-equiv-Eq-Rel : (e : equiv-Eq-Rel) → is-equiv (map-equiv-Eq-Rel e)
  is-equiv-map-equiv-Eq-Rel e = is-equiv-map-equiv (equiv-equiv-Eq-Rel e)

  equiv-sim-equiv-Eq-Rel :
    (e : equiv-Eq-Rel) {x y : A} →
    sim-Eq-Rel R x y ↔
    sim-Eq-Rel S (map-equiv-Eq-Rel e x) (map-equiv-Eq-Rel e y)
  equiv-sim-equiv-Eq-Rel = pr2

  preserves-sim-equiv-Eq-Rel :
    (e : equiv-Eq-Rel) {x y : A} →
    sim-Eq-Rel R x y →
    sim-Eq-Rel S (map-equiv-Eq-Rel e x) (map-equiv-Eq-Rel e y)
  preserves-sim-equiv-Eq-Rel e = pr1 (equiv-sim-equiv-Eq-Rel e)

  hom-equiv-Eq-Rel : equiv-Eq-Rel → hom-Eq-Rel R S
  pr1 (hom-equiv-Eq-Rel e) = map-equiv-Eq-Rel e
  pr2 (hom-equiv-Eq-Rel e) = preserves-sim-equiv-Eq-Rel e

id-equiv-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → equiv-Eq-Rel R R
pr1 (id-equiv-Eq-Rel R) = id-equiv
pr1 (pr2 (id-equiv-Eq-Rel R)) = id
pr2 (pr2 (id-equiv-Eq-Rel R)) = id
```

### Maps between types satisfying the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Rel S (type-Set QS))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Rel R S) →
    is-contr
      ( Σ ( type-Set QR → type-Set QS)
          ( coherence-square-maps
            ( map-hom-Eq-Rel R S h)
            ( map-reflecting-map-Eq-Rel R f)
            ( map-reflecting-map-Eq-Rel S g)))
  unique-map-is-set-quotient Uf Ug h =
    universal-property-set-quotient-is-set-quotient R QR f Uf QS
      ( pair
        ( map-reflecting-map-Eq-Rel S g ∘ map-hom-Eq-Rel R S h)
        ( λ r →
          reflects-map-reflecting-map-Eq-Rel S g
          ( preserves-sim-hom-Eq-Rel R S h r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Rel R S) →
    type-Set QR → type-Set QS
  map-is-set-quotient Uf Ug h =
    pr1 (center (unique-map-is-set-quotient Uf Ug h))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : hom-Eq-Rel R S) →
    coherence-square-maps
      ( map-hom-Eq-Rel R S h)
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-is-set-quotient Uf Ug h)
  coherence-square-map-is-set-quotient Uf Ug h =
    pr2 (center (unique-map-is-set-quotient Uf Ug h))
```

### Functoriality of the set quotient

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  unique-map-set-quotient :
    (h : hom-Eq-Rel R S) →
    is-contr
      ( Σ ( set-quotient R → set-quotient S)
          ( coherence-square-maps
            ( map-hom-Eq-Rel R S h)
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
    (h : hom-Eq-Rel R S) → set-quotient R → set-quotient S
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
    (h : hom-Eq-Rel R S) →
    coherence-square-maps
      ( map-hom-Eq-Rel R S h)
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
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B) {C : UU l5}
  where

  comp-reflecting-map-Eq-Rel :
    reflecting-map-Eq-Rel S C → hom-Eq-Rel R S →
    reflecting-map-Eq-Rel R C
  pr1 (comp-reflecting-map-Eq-Rel g f) =
    map-reflecting-map-Eq-Rel S g ∘ map-hom-Eq-Rel R S f
  pr2 (comp-reflecting-map-Eq-Rel g f) {x} {y} r =
    reflects-map-reflecting-map-Eq-Rel S g (preserves-sim-hom-Eq-Rel R S f r)
```

### Characterizing equality of `hom-Eq-Rel`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  htpy-hom-Eq-Rel : (f g : hom-Eq-Rel R S) → UU (l1 ⊔ l3)
  htpy-hom-Eq-Rel f g = map-hom-Eq-Rel R S f ~ map-hom-Eq-Rel R S g

  refl-htpy-hom-Eq-Rel : (f : hom-Eq-Rel R S) → htpy-hom-Eq-Rel f f
  refl-htpy-hom-Eq-Rel f = refl-htpy

  htpy-eq-hom-Eq-Rel : (f g : hom-Eq-Rel R S) → (f ＝ g) → htpy-hom-Eq-Rel f g
  htpy-eq-hom-Eq-Rel f .f refl = refl-htpy-hom-Eq-Rel f

  is-contr-total-htpy-hom-Eq-Rel :
    (f : hom-Eq-Rel R S) → is-contr (Σ (hom-Eq-Rel R S) (htpy-hom-Eq-Rel f))
  is-contr-total-htpy-hom-Eq-Rel f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-hom-Eq-Rel R S f))
      ( is-prop-preserves-sim-Eq-Rel R S)
      ( map-hom-Eq-Rel R S f)
      ( refl-htpy-hom-Eq-Rel f)
      ( preserves-sim-hom-Eq-Rel R S f)

  is-equiv-htpy-eq-hom-Eq-Rel :
    (f g : hom-Eq-Rel R S) → is-equiv (htpy-eq-hom-Eq-Rel f g)
  is-equiv-htpy-eq-hom-Eq-Rel f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-Eq-Rel f)
      ( htpy-eq-hom-Eq-Rel f)

  extensionality-hom-Eq-Rel :
    (f g : hom-Eq-Rel R S) → (f ＝ g) ≃ htpy-hom-Eq-Rel f g
  pr1 (extensionality-hom-Eq-Rel f g) = htpy-eq-hom-Eq-Rel f g
  pr2 (extensionality-hom-Eq-Rel f g) = is-equiv-htpy-eq-hom-Eq-Rel f g

  eq-htpy-hom-Eq-Rel :
    (f g : hom-Eq-Rel R S) → htpy-hom-Eq-Rel f g → (f ＝ g)
  eq-htpy-hom-Eq-Rel f g = map-inv-equiv (extensionality-hom-Eq-Rel f g)
```

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Rel S (type-Set QS))
  where

  unique-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Rel R S) →
    is-contr
      ( Σ ( type-Set QR ≃ type-Set QS)
          ( λ h' →
            coherence-square-maps
              ( map-equiv-Eq-Rel R S h)
              ( map-reflecting-map-Eq-Rel R f)
              ( map-reflecting-map-Eq-Rel S g)
              ( map-equiv h')))
  unique-equiv-is-set-quotient Uf Ug h =
    uniqueness-set-quotient R QR f Uf QS
      ( comp-reflecting-map-Eq-Rel R S g (hom-equiv-Eq-Rel R S h))
      ( is-set-quotient-is-surjective-and-effective R QS
        ( comp-reflecting-map-Eq-Rel R S g (hom-equiv-Eq-Rel R S h))
        ( ( is-surjective-comp
            ( is-surjective-is-set-quotient S QS g Ug)
            ( is-surjective-is-equiv (is-equiv-map-equiv-Eq-Rel R S h))) ,
          ( λ x y →
            ( inv-equiv
              ( equiv-iff'
                ( prop-Eq-Rel R x y)
                ( prop-Eq-Rel S
                  ( map-equiv-Eq-Rel R S h x)
                  ( map-equiv-Eq-Rel R S h y))
                ( equiv-sim-equiv-Eq-Rel R S h))) ∘e
            ( is-effective-is-set-quotient S QS g Ug
              ( map-equiv-Eq-Rel R S h x)
              ( map-equiv-Eq-Rel R S h y)))))

  equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Rel R S) → type-Set QR ≃ type-Set QS
  equiv-is-set-quotient Uf Ug h =
    pr1 (center (unique-equiv-is-set-quotient Uf Ug h))

  coherence-square-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : equiv-Eq-Rel R S) →
    coherence-square-maps (map-equiv-Eq-Rel R S h)
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-equiv (equiv-is-set-quotient Uf Ug h))
  coherence-square-equiv-is-set-quotient Uf Ug h =
    pr2 (center (unique-equiv-is-set-quotient Uf Ug h))
```

### Functoriality of set quotients preserves identity maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  where

  id-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    map-is-set-quotient R QR f R QR f Uf Uf (id-hom-Eq-Rel R) ~ id
  id-map-is-set-quotient Uf x =
    ap
      ( λ c → pr1 c x)
      { x =
        center
          (unique-map-is-set-quotient R QR f R QR f Uf Uf (id-hom-Eq-Rel R))}
      { y = pair id refl-htpy}
      ( eq-is-contr
        ( unique-map-is-set-quotient R QR f R QR f Uf Uf (id-hom-Eq-Rel R)))

  id-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    htpy-equiv
      ( equiv-is-set-quotient R QR f R QR f Uf Uf (id-equiv-Eq-Rel R))
      ( id-equiv)
  id-equiv-is-set-quotient Uf x =
    ap
      ( λ c → map-equiv (pr1 c) x)
      { x =
        center
          ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf
            ( id-equiv-Eq-Rel R))}
      { y = pair id-equiv refl-htpy}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf
          ( id-equiv-Eq-Rel R)))
```
