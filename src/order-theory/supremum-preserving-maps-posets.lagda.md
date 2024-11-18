# Supremum preserving maps on posets

```agda
module order-theory.supremum-preserving-maps-posets where
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

open import order-theory.join-preserving-maps-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be
{{#concept "supremum preserving" Disambiguation="map of posets" Agda=preserves-suprema-Poset}}
if

```text
  f(⋃ᵢxᵢ) = ⋃ᵢf(xᵢ)
```

for every family `x₍₋₎ : I → P` with a
[supremum](order-theory.least-upper-bounds-posets.md) in `P`.

## Definitions

### The predicate of preserving a supremum

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  {I : UU l5} (x : I → type-Poset P)
  where

  preserves-supremum-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  preserves-supremum-Poset =
    (y : has-least-upper-bound-family-of-elements-Poset P x) →
    is-least-upper-bound-family-of-elements-Poset Q (f ∘ x) (f (pr1 y))

  is-prop-preserves-supremum-Poset :
    is-prop preserves-supremum-Poset
  is-prop-preserves-supremum-Poset =
    is-prop-Π
      ( λ y →
        is-prop-is-least-upper-bound-family-of-elements-Poset Q
          ( f ∘ x)
          ( f (pr1 y)))

  preserves-supremum-prop-Poset : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  preserves-supremum-prop-Poset =
    preserves-supremum-Poset , is-prop-preserves-supremum-Poset
```

### Supremum preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-suprema-Poset :
    (l5 : Level) → (type-Poset P → type-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  preserves-suprema-Poset l5 f =
    {I : UU l5} (x : I → type-Poset P)
    (y : has-least-upper-bound-family-of-elements-Poset P x) →
    is-least-upper-bound-family-of-elements-Poset Q (f ∘ x) (f (pr1 y))

  is-prop-preserves-suprema-Poset :
    {l5 : Level} (f : type-Poset P → type-Poset Q) →
    is-prop (preserves-suprema-Poset l5 f)
  is-prop-preserves-suprema-Poset f =
    is-prop-implicit-Π
      ( λ I → is-prop-Π (is-prop-preserves-supremum-Poset P Q f))

  preserves-suprema-prop-Poset :
    (l5 : Level) →
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  preserves-suprema-prop-Poset l5 f =
    preserves-suprema-Poset l5 f , (is-prop-preserves-suprema-Poset f)

  hom-sup-Poset : (l5 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  hom-sup-Poset l5 =
    Σ (type-Poset P → type-Poset Q) (preserves-suprema-Poset l5)

  map-hom-sup-Poset :
    {l5 : Level} → hom-sup-Poset l5 → type-Poset P → type-Poset Q
  map-hom-sup-Poset = pr1

  preserves-suprema-hom-sup-Poset :
    {l5 : Level} (f : hom-sup-Poset l5) →
    preserves-suprema-Poset l5 (map-hom-sup-Poset f)
  preserves-suprema-hom-sup-Poset = pr2

  sup-map-hom-sup-Poset :
    {l5 : Level} (f : hom-sup-Poset l5) →
    {I : UU l5} {x : I → type-Poset P} →
    has-least-upper-bound-family-of-elements-Poset P x →
    has-least-upper-bound-family-of-elements-Poset Q (map-hom-sup-Poset f ∘ x)
  sup-map-hom-sup-Poset f {x = x} y =
    ( map-hom-sup-Poset f (pr1 y) , preserves-suprema-hom-sup-Poset f x y)
```

## Properties

### Supremum preserving maps preserve suprema over small types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-small-supremum-preserves-suprema-Poset :
    {f : type-Poset P → type-Poset Q} → preserves-suprema-Poset P Q l5 f →
    {I : UU l6} (u : is-small l5 I) (x : I → type-Poset P) →
    preserves-supremum-Poset P Q f (x ∘ map-inv-equiv-is-small u)
  preserves-small-supremum-preserves-suprema-Poset H u x =
    H (x ∘ map-inv-equiv-is-small u)
```

### Supremum preserving maps preserve joins

```text
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-joins-preserves-suprema-Poset :
      {f : type-Poset P → type-Poset Q} →
      preserves-suprema-Poset P Q l5 f →
      preserves-joins-Poset P Q f
    preserves-joins-preserves-suprema-Poset {f} H x y s =
      is-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset
        ( Q)
        ( rec-bool (f x) (f y))
        ( f (pr1 s) , ？) -- TODO
```

> From this property the next would be a simple corollary.

### Supremum preserving maps preserve order

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-order-preserves-suprema-Poset :
      {f : type-Poset P → type-Poset Q} →
      preserves-suprema-Poset P Q l5 f →
      preserves-order-Poset P Q f
    preserves-order-preserves-suprema-Poset {f} H x y p =
      pr2
        ( preserves-small-supremum-preserves-suprema-Poset P Q H
          ( Raise l5 bool)
          ( family-of-elements-has-least-binary-upper-bound-Poset P x y
            ( has-least-binary-upper-bound-leq-Poset P x y p))
          ( y ,
            λ z →
            ( ( ev (map-raise false)) ,
              ( λ where
                u (map-raise true) → transitive-leq-Poset P x y z u p
                u (map-raise false) → u)))
          ( f y))
        ( refl-leq-Poset Q (f y))
        ( map-raise true)
```

### Homotopies of supremum preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-hom-sup-Poset : (f g : hom-sup-Poset P Q l5) → UU (l1 ⊔ l3)
  htpy-hom-sup-Poset f g = map-hom-sup-Poset P Q f ~ map-hom-sup-Poset P Q g

  refl-htpy-hom-sup-Poset : (f : hom-sup-Poset P Q l5) → htpy-hom-sup-Poset f f
  refl-htpy-hom-sup-Poset f = refl-htpy

  htpy-eq-hom-sup-Poset :
    (f g : hom-sup-Poset P Q l5) → f ＝ g → htpy-hom-sup-Poset f g
  htpy-eq-hom-sup-Poset f .f refl = refl-htpy-hom-sup-Poset f

  is-torsorial-htpy-hom-sup-Poset :
    (f : hom-sup-Poset P Q l5) → is-torsorial (htpy-hom-sup-Poset f)
  is-torsorial-htpy-hom-sup-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-hom-sup-Poset P Q f))
      ( is-prop-preserves-suprema-Poset P Q)
      ( map-hom-sup-Poset P Q f)
      ( refl-htpy)
      ( preserves-suprema-hom-sup-Poset P Q f)

  is-equiv-htpy-eq-hom-sup-Poset :
    (f g : hom-sup-Poset P Q l5) → is-equiv (htpy-eq-hom-sup-Poset f g)
  is-equiv-htpy-eq-hom-sup-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-sup-Poset f)
      ( htpy-eq-hom-sup-Poset f)

  extensionality-hom-sup-Poset :
    (f g : hom-sup-Poset P Q l5) → (f ＝ g) ≃ htpy-hom-sup-Poset f g
  pr1 (extensionality-hom-sup-Poset f g) = htpy-eq-hom-sup-Poset f g
  pr2 (extensionality-hom-sup-Poset f g) = is-equiv-htpy-eq-hom-sup-Poset f g

  eq-htpy-hom-sup-Poset :
    (f g : hom-sup-Poset P Q l5) → htpy-hom-sup-Poset f g → f ＝ g
  eq-htpy-hom-sup-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-sup-Poset f g)
```

### The identity supremum preserving map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-suprema-id-Poset :
    {l3 : Level} → preserves-suprema-Poset P P l3 (id {A = type-Poset P})
  preserves-suprema-id-Poset x y = pr2 y

  id-hom-sup-Poset : (l3 : Level) → hom-sup-Poset P P l3
  id-hom-sup-Poset l3 = id , preserves-suprema-id-Poset
```

### Composing supremum preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  preserves-suprema-comp-Poset :
    (g : hom-sup-Poset Q R l7) (f : hom-sup-Poset P Q l7) →
    preserves-suprema-Poset P R l7
      ( map-hom-sup-Poset Q R g ∘ map-hom-sup-Poset P Q f)
  preserves-suprema-comp-Poset g f x y =
    preserves-suprema-hom-sup-Poset Q R g
      ( map-hom-sup-Poset P Q f ∘ x)
      ( sup-map-hom-sup-Poset P Q f y)

  comp-hom-sup-Poset :
    (g : hom-sup-Poset Q R l7) (f : hom-sup-Poset P Q l7) →
    hom-sup-Poset P R l7
  comp-hom-sup-Poset g f =
    map-hom-sup-Poset Q R g ∘ map-hom-sup-Poset P Q f ,
    preserves-suprema-comp-Poset g f
```

### Unit laws for composition of supremum preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-hom-sup-Poset :
    (f : hom-sup-Poset P Q l5) →
    ( comp-hom-sup-Poset P Q Q (id-hom-sup-Poset Q l5) f) ＝ f
  left-unit-law-comp-hom-sup-Poset f =
    eq-htpy-hom-sup-Poset P Q
      ( comp-hom-sup-Poset P Q Q (id-hom-sup-Poset Q l5) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-sup-Poset :
    (f : hom-sup-Poset P Q l5) →
    (comp-hom-sup-Poset P P Q f (id-hom-sup-Poset P l5)) ＝ f
  right-unit-law-comp-hom-sup-Poset f =
    eq-htpy-hom-sup-Poset P Q
      ( comp-hom-sup-Poset P P Q f (id-hom-sup-Poset P l5))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of supremum preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : hom-sup-Poset R S l9)
  (g : hom-sup-Poset Q R l9)
  (f : hom-sup-Poset P Q l9)
  where

  associative-comp-hom-sup-Poset :
    comp-hom-sup-Poset P Q S (comp-hom-sup-Poset Q R S h g) f ＝
    comp-hom-sup-Poset P R S h (comp-hom-sup-Poset P Q R g f)
  associative-comp-hom-sup-Poset =
    eq-htpy-hom-sup-Poset P S
      ( comp-hom-sup-Poset P Q S (comp-hom-sup-Poset Q R S h g) f)
      ( comp-hom-sup-Poset P R S h (comp-hom-sup-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-hom-sup-Poset :
    comp-hom-sup-Poset P Q S (comp-hom-sup-Poset Q R S h g) f ＝ⁱ
    comp-hom-sup-Poset P R S h (comp-hom-sup-Poset P Q R g f)
  involutive-eq-associative-comp-hom-sup-Poset =
    involutive-eq-eq associative-comp-hom-sup-Poset
```
