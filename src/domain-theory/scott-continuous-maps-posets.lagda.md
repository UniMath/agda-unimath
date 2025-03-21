# Scott-continuous maps between posets

```agda
module domain-theory.scott-continuous-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets
open import domain-theory.reindexing-directed-families-posets

open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.strictly-involutive-identity-types
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the carrier types of two
[posets](order-theory.posets.md) is said to be
{{#concept "Scott-continuous" Disambiguation="map of posets" WD="Scott continuity" WDID=Q895815 Agda=scott-continuous-hom-Poset}}
if

```text
  f(⋃ᵢxᵢ) = ⋃ᵢf(xᵢ)
```

for every [directed family](domain-theory.directed-families-posets.md)
`x₍₋₎ : I → P` with a [supremum](order-theory.least-upper-bounds-posets.md) in
`P`.

## Definitions

### The predicate of preserving the supremum of a directed family

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  (x : directed-family-Poset l5 P)
  where

  preserves-supremum-directed-family-map-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  preserves-supremum-directed-family-map-Poset =
    (y :
      has-least-upper-bound-family-of-elements-Poset P
        ( family-directed-family-Poset P x)) →
    is-least-upper-bound-family-of-elements-Poset Q
      ( f ∘ family-directed-family-Poset P x)
      ( f (pr1 y))

  is-prop-preserves-supremum-directed-family-map-Poset :
    is-prop preserves-supremum-directed-family-map-Poset
  is-prop-preserves-supremum-directed-family-map-Poset =
    is-prop-Π
      ( λ y →
        is-prop-is-least-upper-bound-family-of-elements-Poset Q
          ( f ∘ family-directed-family-Poset P x)
          ( f (pr1 y)))

  preserves-supremum-directed-family-prop-map-Poset :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  preserves-supremum-directed-family-prop-map-Poset =
    preserves-supremum-directed-family-map-Poset ,
    is-prop-preserves-supremum-directed-family-map-Poset
```

### The predicate on a map of posets of being Scott-continuous

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  is-scott-continuous-Poset :
    (l5 : Level) → (type-Poset P → type-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  is-scott-continuous-Poset l5 f =
    (x : directed-family-Poset l5 P)
    (y :
      has-least-upper-bound-family-of-elements-Poset P
        ( family-directed-family-Poset P x)) →
    is-least-upper-bound-family-of-elements-Poset Q
      ( f ∘ family-directed-family-Poset P x)
      ( f (pr1 y))

  is-prop-is-scott-continuous-Poset :
    {l5 : Level} (f : type-Poset P → type-Poset Q) →
    is-prop (is-scott-continuous-Poset l5 f)
  is-prop-is-scott-continuous-Poset f =
    is-prop-Π (is-prop-preserves-supremum-directed-family-map-Poset P Q f)

  is-scott-continuous-prop-Poset :
    (l5 : Level) →
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  is-scott-continuous-prop-Poset l5 f =
    ( is-scott-continuous-Poset l5 f) ,
    ( is-prop-is-scott-continuous-Poset f)

  scott-continuous-hom-Poset : (l5 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  scott-continuous-hom-Poset l5 =
    Σ (type-Poset P → type-Poset Q) (is-scott-continuous-Poset l5)

  map-scott-continuous-hom-Poset :
    {l5 : Level} → scott-continuous-hom-Poset l5 → type-Poset P → type-Poset Q
  map-scott-continuous-hom-Poset = pr1

  is-scott-continuous-map-scott-continuous-hom-Poset :
    {l5 : Level} (f : scott-continuous-hom-Poset l5) →
    is-scott-continuous-Poset l5 (map-scott-continuous-hom-Poset f)
  is-scott-continuous-map-scott-continuous-hom-Poset = pr2

  sup-map-scott-continuous-hom-Poset :
    {l5 : Level} (f : scott-continuous-hom-Poset l5) →
    (x : directed-family-Poset l5 P) →
    has-least-upper-bound-family-of-elements-Poset P
      ( family-directed-family-Poset P x) →
    has-least-upper-bound-family-of-elements-Poset Q
      ( map-scott-continuous-hom-Poset f ∘ family-directed-family-Poset P x)
  sup-map-scott-continuous-hom-Poset f x y =
    ( map-scott-continuous-hom-Poset f (pr1 y) ,
      is-scott-continuous-map-scott-continuous-hom-Poset f x y)
```

## Properties

### Scott-continuous maps preserve suprema of directed families over small indexing types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-small-supremum-directed-family-is-scott-continuous-Poset :
    {f : type-Poset P → type-Poset Q} →
    is-scott-continuous-Poset P Q l5 f →
    (x : directed-family-Poset l6 P)
    (u : is-small l5 (type-directed-family-Poset P x)) →
    preserves-supremum-directed-family-map-Poset P Q f
      ( reindex-inv-equiv-directed-family-Poset P x (equiv-is-small u))
  preserves-small-supremum-directed-family-is-scott-continuous-Poset H x u =
    H (reindex-inv-equiv-directed-family-Poset P x (equiv-is-small u))
```

### Scott-continuous maps preserve order

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-order-is-scott-continuous-Poset :
      {f : type-Poset P → type-Poset Q} →
      is-scott-continuous-Poset P Q l5 f →
      preserves-order-Poset P Q f
    preserves-order-is-scott-continuous-Poset {f} H x y p =
      pr2
        ( preserves-small-supremum-directed-family-is-scott-continuous-Poset
          ( P)
          ( Q)
          ( H)
          ( ( bool , unit-trunc-Prop true) ,
            rec-bool x y ,
            λ where
            true true →
              intro-exists true (refl-leq-Poset P x , refl-leq-Poset P x)
            true false →
              intro-exists false (p , refl-leq-Poset P y)
            false true →
              intro-exists false (refl-leq-Poset P y , p)
            false false →
              intro-exists false (refl-leq-Poset P y , refl-leq-Poset P y))
          ( Raise l5 bool)
          ( y ,
            λ z →
            ( ( ev (map-raise false)) ,
              ( λ where
                u (map-raise true) → transitive-leq-Poset P x y z u p
                u (map-raise false) → u)))
          ( f y))
        ( refl-leq-Poset Q (f y))
        ( map-raise true)

  hom-scott-continuous-hom-Poset :
    scott-continuous-hom-Poset P Q l5 → hom-Poset P Q
  hom-scott-continuous-hom-Poset f =
    map-scott-continuous-hom-Poset P Q f ,
    preserves-order-is-scott-continuous-Poset
      ( is-scott-continuous-map-scott-continuous-hom-Poset P Q f)
```

### Homotopies of Scott-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-scott-continuous-hom-Poset :
    (f g : scott-continuous-hom-Poset P Q l5) → UU (l1 ⊔ l3)
  htpy-scott-continuous-hom-Poset f g =
    map-scott-continuous-hom-Poset P Q f ~ map-scott-continuous-hom-Poset P Q g

  refl-htpy-scott-continuous-hom-Poset :
    (f : scott-continuous-hom-Poset P Q l5) →
    htpy-scott-continuous-hom-Poset f f
  refl-htpy-scott-continuous-hom-Poset f = refl-htpy

  htpy-eq-scott-continuous-hom-Poset :
    (f g : scott-continuous-hom-Poset P Q l5) →
    f ＝ g →
    htpy-scott-continuous-hom-Poset f g
  htpy-eq-scott-continuous-hom-Poset f .f refl =
    refl-htpy-scott-continuous-hom-Poset f

  is-torsorial-htpy-scott-continuous-hom-Poset :
    (f : scott-continuous-hom-Poset P Q l5) →
    is-torsorial (htpy-scott-continuous-hom-Poset f)
  is-torsorial-htpy-scott-continuous-hom-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-scott-continuous-hom-Poset P Q f))
      ( is-prop-is-scott-continuous-Poset P Q)
      ( map-scott-continuous-hom-Poset P Q f)
      ( refl-htpy)
      ( is-scott-continuous-map-scott-continuous-hom-Poset P Q f)

  is-equiv-htpy-eq-scott-continuous-hom-Poset :
    (f g : scott-continuous-hom-Poset P Q l5) →
    is-equiv (htpy-eq-scott-continuous-hom-Poset f g)
  is-equiv-htpy-eq-scott-continuous-hom-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-scott-continuous-hom-Poset f)
      ( htpy-eq-scott-continuous-hom-Poset f)

  extensionality-scott-continuous-hom-Poset :
    (f g : scott-continuous-hom-Poset P Q l5) →
    (f ＝ g) ≃ htpy-scott-continuous-hom-Poset f g
  pr1 (extensionality-scott-continuous-hom-Poset f g) =
    htpy-eq-scott-continuous-hom-Poset f g
  pr2 (extensionality-scott-continuous-hom-Poset f g) =
    is-equiv-htpy-eq-scott-continuous-hom-Poset f g

  eq-htpy-scott-continuous-hom-Poset :
    (f g : scott-continuous-hom-Poset P Q l5) →
    htpy-scott-continuous-hom-Poset f g → f ＝ g
  eq-htpy-scott-continuous-hom-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-scott-continuous-hom-Poset f g)
```

### The identity Scott-continuous map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-scott-continuous-id-hom-Poset :
    {l3 : Level} → is-scott-continuous-Poset P P l3 (id {A = type-Poset P})
  is-scott-continuous-id-hom-Poset x = pr2

  id-scott-continuous-hom-Poset :
    (l3 : Level) → scott-continuous-hom-Poset P P l3
  id-scott-continuous-hom-Poset l3 = id , is-scott-continuous-id-hom-Poset
```

### Composing Scott-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  is-scott-continuous-comp-scott-continuous-hom-Poset :
    (g : scott-continuous-hom-Poset Q R l7)
    (f : scott-continuous-hom-Poset P Q l7) →
    is-scott-continuous-Poset P R l7
      ( map-scott-continuous-hom-Poset Q R g ∘
        map-scott-continuous-hom-Poset P Q f)
  is-scott-continuous-comp-scott-continuous-hom-Poset g f x y =
    is-scott-continuous-map-scott-continuous-hom-Poset Q R g
      ( directed-family-hom-Poset P Q (hom-scott-continuous-hom-Poset P Q f) x)
      ( sup-map-scott-continuous-hom-Poset P Q f x y)

  comp-scott-continuous-hom-Poset :
    (g : scott-continuous-hom-Poset Q R l7)
    (f : scott-continuous-hom-Poset P Q l7) →
    scott-continuous-hom-Poset P R l7
  comp-scott-continuous-hom-Poset g f =
    map-scott-continuous-hom-Poset Q R g ∘
    map-scott-continuous-hom-Poset P Q f ,
    is-scott-continuous-comp-scott-continuous-hom-Poset g f
```

### Unit laws for composition of Scott-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-scott-continuous-hom-Poset :
    (f : scott-continuous-hom-Poset P Q l5) →
    ( comp-scott-continuous-hom-Poset P Q Q
      ( id-scott-continuous-hom-Poset Q l5)
      ( f)) ＝
    ( f)
  left-unit-law-comp-scott-continuous-hom-Poset f =
    eq-htpy-scott-continuous-hom-Poset P Q
      ( comp-scott-continuous-hom-Poset P Q Q
        ( id-scott-continuous-hom-Poset Q l5)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-scott-continuous-hom-Poset :
    (f : scott-continuous-hom-Poset P Q l5) →
    ( comp-scott-continuous-hom-Poset P P Q
      ( f)
      ( id-scott-continuous-hom-Poset P l5)) ＝
    ( f)
  right-unit-law-comp-scott-continuous-hom-Poset f =
    eq-htpy-scott-continuous-hom-Poset P Q
      ( comp-scott-continuous-hom-Poset P P Q
        ( f)
        ( id-scott-continuous-hom-Poset P l5))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of Scott-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : scott-continuous-hom-Poset R S l9)
  (g : scott-continuous-hom-Poset Q R l9)
  (f : scott-continuous-hom-Poset P Q l9)
  where

  associative-comp-scott-continuous-hom-Poset :
    comp-scott-continuous-hom-Poset P Q S
      ( comp-scott-continuous-hom-Poset Q R S h g)
      ( f) ＝
    comp-scott-continuous-hom-Poset P R S
      ( h)
      ( comp-scott-continuous-hom-Poset P Q R g f)
  associative-comp-scott-continuous-hom-Poset =
    eq-htpy-scott-continuous-hom-Poset P S
      ( comp-scott-continuous-hom-Poset P Q S
        ( comp-scott-continuous-hom-Poset Q R S h g)
        ( f))
      ( comp-scott-continuous-hom-Poset P R S
        ( h)
        ( comp-scott-continuous-hom-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-scott-continuous-hom-Poset :
    comp-scott-continuous-hom-Poset P Q S
      ( comp-scott-continuous-hom-Poset Q R S h g)
      ( f) ＝ⁱ
    comp-scott-continuous-hom-Poset P R S
      ( h)
      ( comp-scott-continuous-hom-Poset P Q R g f)
  involutive-eq-associative-comp-scott-continuous-hom-Poset =
    involutive-eq-eq associative-comp-scott-continuous-hom-Poset
```
