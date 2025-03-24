# Join preserving maps between posets

```agda
module order-theory.join-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.small-types
open import foundation.strictly-involutive-identity-types
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.raising-universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be
{{#concept "join preserving" Disambiguation="map of posets" Agda=preserves-joins-Poset}}
if for every pair of elements `x, y : P` with a
[least upper bound](order-theory.least-upper-bounds-posets.md) `z`, we have
`f z` is the least upper bound of `f x` and `f y`.

## Definitions

### The predicate of preserving a join

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  (x y : type-Poset P)
  where

  preserves-join-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-join-Poset =
    (s : has-least-binary-upper-bound-Poset P x y) →
    is-least-binary-upper-bound-Poset Q (f x) (f y) (f (pr1 s))

  is-prop-preserves-join-Poset :
    is-prop preserves-join-Poset
  is-prop-preserves-join-Poset =
    is-prop-Π
      ( λ s →
        is-prop-is-least-binary-upper-bound-Poset Q
          ( f x)
          ( f y)
          ( f (pr1 s)))

  preserves-join-prop-Poset : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-join-prop-Poset =
    preserves-join-Poset , is-prop-preserves-join-Poset
```

### Join preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-joins-Poset :
    (type-Poset P → type-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-joins-Poset f =
    (x y : type-Poset P)
    (s : has-least-binary-upper-bound-Poset P x y) →
    is-least-binary-upper-bound-Poset Q (f x) (f y) (f (pr1 s))

  is-prop-preserves-joins-Poset :
    (f : type-Poset P → type-Poset Q) →
    is-prop (preserves-joins-Poset f)
  is-prop-preserves-joins-Poset f =
    is-prop-Π
      ( λ x → is-prop-Π (is-prop-preserves-join-Poset P Q f x))

  preserves-joins-prop-Poset :
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-joins-prop-Poset f =
    ( preserves-joins-Poset f , is-prop-preserves-joins-Poset f)

  join-preserving-hom-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  join-preserving-hom-Poset =
    Σ (type-Poset P → type-Poset Q) (preserves-joins-Poset)

  map-join-preserving-hom-Poset :
    join-preserving-hom-Poset → type-Poset P → type-Poset Q
  map-join-preserving-hom-Poset = pr1

  preserves-joins-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset) →
    preserves-joins-Poset (map-join-preserving-hom-Poset f)
  preserves-joins-join-preserving-hom-Poset = pr2

  sup-map-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset) {x y : type-Poset P} →
    has-least-binary-upper-bound-Poset P x y →
    has-least-binary-upper-bound-Poset Q
      ( map-join-preserving-hom-Poset f x)
      ( map-join-preserving-hom-Poset f y)
  sup-map-join-preserving-hom-Poset f {x} {y} s =
    ( map-join-preserving-hom-Poset f (pr1 s) ,
      preserves-joins-join-preserving-hom-Poset f x y s)
```

## Properties

### Join preserving maps preserve order

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-order-preserves-joins-Poset :
      {f : type-Poset P → type-Poset Q} →
      preserves-joins-Poset P Q f →
      preserves-order-Poset P Q f
    preserves-order-preserves-joins-Poset {f} H x y p =
      pr1
        ( pr2
          ( H x y (y , is-least-binary-upper-bound-leq-Poset P x y p) (f y))
          ( refl-leq-Poset Q (f y)))
```

### Homotopies of join preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-join-preserving-hom-Poset :
    (f g : join-preserving-hom-Poset P Q) → UU (l1 ⊔ l3)
  htpy-join-preserving-hom-Poset f g =
    map-join-preserving-hom-Poset P Q f ~ map-join-preserving-hom-Poset P Q g

  refl-htpy-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset P Q) → htpy-join-preserving-hom-Poset f f
  refl-htpy-join-preserving-hom-Poset f = refl-htpy

  htpy-eq-join-preserving-hom-Poset :
    (f g : join-preserving-hom-Poset P Q) →
    f ＝ g → htpy-join-preserving-hom-Poset f g
  htpy-eq-join-preserving-hom-Poset f .f refl =
    refl-htpy-join-preserving-hom-Poset f

  is-torsorial-htpy-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset P Q) →
    is-torsorial (htpy-join-preserving-hom-Poset f)
  is-torsorial-htpy-join-preserving-hom-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-join-preserving-hom-Poset P Q f))
      ( is-prop-preserves-joins-Poset P Q)
      ( map-join-preserving-hom-Poset P Q f)
      ( refl-htpy)
      ( preserves-joins-join-preserving-hom-Poset P Q f)

  is-equiv-htpy-eq-join-preserving-hom-Poset :
    (f g : join-preserving-hom-Poset P Q) →
    is-equiv (htpy-eq-join-preserving-hom-Poset f g)
  is-equiv-htpy-eq-join-preserving-hom-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-join-preserving-hom-Poset f)
      ( htpy-eq-join-preserving-hom-Poset f)

  extensionality-join-preserving-hom-Poset :
    (f g : join-preserving-hom-Poset P Q) →
    (f ＝ g) ≃ htpy-join-preserving-hom-Poset f g
  pr1 (extensionality-join-preserving-hom-Poset f g) =
    htpy-eq-join-preserving-hom-Poset f g
  pr2 (extensionality-join-preserving-hom-Poset f g) =
    is-equiv-htpy-eq-join-preserving-hom-Poset f g

  eq-htpy-join-preserving-hom-Poset :
    (f g : join-preserving-hom-Poset P Q) →
    htpy-join-preserving-hom-Poset f g → f ＝ g
  eq-htpy-join-preserving-hom-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-join-preserving-hom-Poset f g)
```

### The identity join preserving map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-joins-id-hom-Poset :
    preserves-joins-Poset P P (id {A = type-Poset P})
  preserves-joins-id-hom-Poset x y s = pr2 s

  id-join-preserving-hom-Poset : join-preserving-hom-Poset P P
  id-join-preserving-hom-Poset = id , preserves-joins-id-hom-Poset
```

### Composing join preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  preserves-joins-comp-join-preserving-hom-Poset :
    (g : join-preserving-hom-Poset Q R)
    (f : join-preserving-hom-Poset P Q) →
    preserves-joins-Poset P R
      ( map-join-preserving-hom-Poset Q R g ∘
        map-join-preserving-hom-Poset P Q f)
  preserves-joins-comp-join-preserving-hom-Poset g f x y s =
    preserves-joins-join-preserving-hom-Poset Q R g
      ( map-join-preserving-hom-Poset P Q f x)
      ( map-join-preserving-hom-Poset P Q f y)
      ( sup-map-join-preserving-hom-Poset P Q f s)

  comp-join-preserving-hom-Poset :
    (g : join-preserving-hom-Poset Q R) (f : join-preserving-hom-Poset P Q) →
    join-preserving-hom-Poset P R
  comp-join-preserving-hom-Poset g f =
    map-join-preserving-hom-Poset Q R g ∘ map-join-preserving-hom-Poset P Q f ,
    preserves-joins-comp-join-preserving-hom-Poset g f
```

### Unit laws for composition of join preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset P Q) →
    comp-join-preserving-hom-Poset P Q Q (id-join-preserving-hom-Poset Q) f ＝ f
  left-unit-law-comp-join-preserving-hom-Poset f =
    eq-htpy-join-preserving-hom-Poset P Q
      ( comp-join-preserving-hom-Poset P Q Q (id-join-preserving-hom-Poset Q) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-join-preserving-hom-Poset :
    (f : join-preserving-hom-Poset P Q) →
    comp-join-preserving-hom-Poset P P Q f (id-join-preserving-hom-Poset P) ＝ f
  right-unit-law-comp-join-preserving-hom-Poset f =
    eq-htpy-join-preserving-hom-Poset P Q
      ( comp-join-preserving-hom-Poset P P Q f (id-join-preserving-hom-Poset P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of join preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : join-preserving-hom-Poset R S)
  (g : join-preserving-hom-Poset Q R)
  (f : join-preserving-hom-Poset P Q)
  where

  associative-comp-join-preserving-hom-Poset :
    comp-join-preserving-hom-Poset P Q S
      ( comp-join-preserving-hom-Poset Q R S h g)
      ( f) ＝
    comp-join-preserving-hom-Poset P R S
      ( h)
      ( comp-join-preserving-hom-Poset P Q R g f)
  associative-comp-join-preserving-hom-Poset =
    eq-htpy-join-preserving-hom-Poset P S
      ( comp-join-preserving-hom-Poset P Q S
        ( comp-join-preserving-hom-Poset Q R S h g)
        ( f))
      ( comp-join-preserving-hom-Poset P R S
        ( h)
        ( comp-join-preserving-hom-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-join-preserving-hom-Poset :
    comp-join-preserving-hom-Poset P Q S
      ( comp-join-preserving-hom-Poset Q R S h g)
      ( f) ＝ⁱ
    comp-join-preserving-hom-Poset P R S
      ( h)
      ( comp-join-preserving-hom-Poset P Q R g f)
  involutive-eq-associative-comp-join-preserving-hom-Poset =
    involutive-eq-eq associative-comp-join-preserving-hom-Poset
```
