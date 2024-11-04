# Join preserving maps on posets

```agda
module order-theory.join-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.strictly-involutive-identity-types
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be
{{#concept "join preserving" Disambiguation="map of posets" Agda=preserves-joins-map-Poset}}
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

  preserves-join-map-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-join-map-Poset =
    (s : has-least-binary-upper-bound-Poset P x y) →
    is-least-binary-upper-bound-Poset Q (f x) (f y) (f (pr1 s))

  is-prop-preserves-join-map-Poset :
    is-prop preserves-join-map-Poset
  is-prop-preserves-join-map-Poset =
    is-prop-Π
      ( λ s →
        is-prop-is-least-binary-upper-bound-Poset Q
          ( f x)
          ( f y)
          ( f (pr1 s)))

  preserves-join-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-join-prop-map-Poset =
    preserves-join-map-Poset , is-prop-preserves-join-map-Poset
```

### Join preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-joins-map-Poset :
    (type-Poset P → type-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-joins-map-Poset f =
    (x y : type-Poset P)
    (s : has-least-binary-upper-bound-Poset P x y) →
    is-least-binary-upper-bound-Poset Q (f x) (f y) (f (pr1 s))

  is-prop-preserves-joins-map-Poset :
    (f : type-Poset P → type-Poset Q) →
    is-prop (preserves-joins-map-Poset f)
  is-prop-preserves-joins-map-Poset f =
    is-prop-Π
      ( λ x → is-prop-Π (is-prop-preserves-join-map-Poset P Q f x))

  preserves-joins-prop-map-Poset :
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-joins-prop-map-Poset f =
    ( preserves-joins-map-Poset f , is-prop-preserves-joins-map-Poset f)

  hom-join-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-join-Poset =
    Σ (type-Poset P → type-Poset Q) (preserves-joins-map-Poset)

  map-hom-join-Poset : hom-join-Poset → type-Poset P → type-Poset Q
  map-hom-join-Poset = pr1

  preserves-joins-map-hom-join-Poset :
    (f : hom-join-Poset) →
    preserves-joins-map-Poset (map-hom-join-Poset f)
  preserves-joins-map-hom-join-Poset = pr2

  sup-map-hom-join-Poset :
    (f : hom-join-Poset) {x y : type-Poset P} →
    has-least-binary-upper-bound-Poset P x y →
    has-least-binary-upper-bound-Poset Q
      ( map-hom-join-Poset f x)
      ( map-hom-join-Poset f y)
  sup-map-hom-join-Poset f {x} {y} s =
    ( map-hom-join-Poset f (pr1 s) , preserves-joins-map-hom-join-Poset f x y s)
```

## Properties

### Join preserving maps preserve order

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-order-preserves-joins-map-Poset :
      {f : type-Poset P → type-Poset Q} →
      preserves-joins-map-Poset P Q f →
      preserves-order-Poset P Q f
    preserves-order-preserves-joins-map-Poset {f} H x y p =
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

  htpy-hom-join-Poset : (f g : hom-join-Poset P Q) → UU (l1 ⊔ l3)
  htpy-hom-join-Poset f g = map-hom-join-Poset P Q f ~ map-hom-join-Poset P Q g

  refl-htpy-hom-join-Poset : (f : hom-join-Poset P Q) → htpy-hom-join-Poset f f
  refl-htpy-hom-join-Poset f = refl-htpy

  htpy-eq-hom-join-Poset :
    (f g : hom-join-Poset P Q) → f ＝ g → htpy-hom-join-Poset f g
  htpy-eq-hom-join-Poset f .f refl = refl-htpy-hom-join-Poset f

  is-torsorial-htpy-hom-join-Poset :
    (f : hom-join-Poset P Q) → is-torsorial (htpy-hom-join-Poset f)
  is-torsorial-htpy-hom-join-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-hom-join-Poset P Q f))
      ( is-prop-preserves-joins-map-Poset P Q)
      ( map-hom-join-Poset P Q f)
      ( refl-htpy)
      ( preserves-joins-map-hom-join-Poset P Q f)

  is-equiv-htpy-eq-hom-join-Poset :
    (f g : hom-join-Poset P Q) → is-equiv (htpy-eq-hom-join-Poset f g)
  is-equiv-htpy-eq-hom-join-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-join-Poset f)
      ( htpy-eq-hom-join-Poset f)

  extensionality-hom-join-Poset :
    (f g : hom-join-Poset P Q) → (f ＝ g) ≃ htpy-hom-join-Poset f g
  pr1 (extensionality-hom-join-Poset f g) = htpy-eq-hom-join-Poset f g
  pr2 (extensionality-hom-join-Poset f g) = is-equiv-htpy-eq-hom-join-Poset f g

  eq-htpy-hom-join-Poset :
    (f g : hom-join-Poset P Q) → htpy-hom-join-Poset f g → f ＝ g
  eq-htpy-hom-join-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-join-Poset f g)
```

### The identity join preserving map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-joins-id-Poset :
    preserves-joins-map-Poset P P (id {A = type-Poset P})
  preserves-joins-id-Poset x y s = pr2 s

  id-hom-join-Poset : hom-join-Poset P P
  id-hom-join-Poset = id , preserves-joins-id-Poset
```

### Composing join preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  preserves-joins-comp-Poset :
    (g : hom-join-Poset Q R) (f : hom-join-Poset P Q) →
    preserves-joins-map-Poset P R
      ( map-hom-join-Poset Q R g ∘ map-hom-join-Poset P Q f)
  preserves-joins-comp-Poset g f x y s =
    preserves-joins-map-hom-join-Poset Q R g
      ( map-hom-join-Poset P Q f x)
      ( map-hom-join-Poset P Q f y)
      ( sup-map-hom-join-Poset P Q f s)

  comp-hom-join-Poset :
    (g : hom-join-Poset Q R) (f : hom-join-Poset P Q) →
    hom-join-Poset P R
  comp-hom-join-Poset g f =
    map-hom-join-Poset Q R g ∘ map-hom-join-Poset P Q f ,
    preserves-joins-comp-Poset g f
```

### Unit laws for composition of join preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-hom-join-Poset :
    (f : hom-join-Poset P Q) →
    ( comp-hom-join-Poset P Q Q (id-hom-join-Poset Q) f) ＝ f
  left-unit-law-comp-hom-join-Poset f =
    eq-htpy-hom-join-Poset P Q
      ( comp-hom-join-Poset P Q Q (id-hom-join-Poset Q) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-join-Poset :
    (f : hom-join-Poset P Q) →
    (comp-hom-join-Poset P P Q f (id-hom-join-Poset P)) ＝ f
  right-unit-law-comp-hom-join-Poset f =
    eq-htpy-hom-join-Poset P Q
      ( comp-hom-join-Poset P P Q f (id-hom-join-Poset P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of join preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : hom-join-Poset R S)
  (g : hom-join-Poset Q R)
  (f : hom-join-Poset P Q)
  where

  associative-comp-hom-join-Poset :
    comp-hom-join-Poset P Q S (comp-hom-join-Poset Q R S h g) f ＝
    comp-hom-join-Poset P R S h (comp-hom-join-Poset P Q R g f)
  associative-comp-hom-join-Poset =
    eq-htpy-hom-join-Poset P S
      ( comp-hom-join-Poset P Q S (comp-hom-join-Poset Q R S h g) f)
      ( comp-hom-join-Poset P R S h (comp-hom-join-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-hom-join-Poset :
    comp-hom-join-Poset P Q S (comp-hom-join-Poset Q R S h g) f ＝ⁱ
    comp-hom-join-Poset P R S h (comp-hom-join-Poset P Q R g f)
  involutive-eq-associative-comp-hom-join-Poset =
    involutive-eq-eq associative-comp-hom-join-Poset
```
