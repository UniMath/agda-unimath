# ω-Continuous maps between posets

```agda
module domain-theory.omega-continuous-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets

open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.dependent-pair-types
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
open import foundation.strictly-involutive-identity-types
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.increasing-sequences-posets
open import order-theory.join-preserving-maps-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the carrier types of two
[posets](order-theory.posets.md) is said to be
{{#concept "ω-continuous" Disambiguation="map of posets" Agda=ω-continuous-hom-Poset}}
if it maps the supremum of every ascending
ω-[chain](order-theory.chains-posets.md)

```text
  x₀ ≤ x₁ ≤ x₂ ≤ ­… ≤ xₙ ≤ xₙ₊₁ ≤ … ≤ xω
```

to the supremum of the image of the ascending chain

```text
  { f xᵢ | i : ℕ }
```

In other words, `f(⋃ᵢxᵢ) = ⋃ᵢf(xᵢ)` for all ascending chains `x₍₋₎ : ℕ → P`. It
follows that `f` preserves the order of `P` if it is ω-continuous.

The ω-continuity condition is a proper generalization of
[Scott-continuity](domain-theory.scott-continuous-maps-posets.md) for which
[Kleene's fixed point theorem](domain-theory.kleenes-fixed-point-theorem-omega-complete-posets.md)
still applies.

## Definitions

### The predicate of preserving the supremum of an ω-chain

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  (x : hom-Poset ℕ-Poset P)
  where

  preserves-ω-supremum-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-ω-supremum-Poset =
    (y :
      has-least-upper-bound-family-of-elements-Poset P
        ( map-hom-Poset ℕ-Poset P x)) →
    is-least-upper-bound-family-of-elements-Poset Q
      ( f ∘ map-hom-Poset ℕ-Poset P x)
      ( f (pr1 y))

  is-prop-preserves-ω-supremum-Poset :
    is-prop preserves-ω-supremum-Poset
  is-prop-preserves-ω-supremum-Poset =
    is-prop-Π
      ( λ y →
        is-prop-is-least-upper-bound-family-of-elements-Poset Q
          ( f ∘ map-hom-Poset ℕ-Poset P x)
          ( f (pr1 y)))

  preserves-ω-supremum-prop-Poset :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-ω-supremum-prop-Poset =
    preserves-ω-supremum-Poset ,
    is-prop-preserves-ω-supremum-Poset
```

### The predicate on a map of posets of being ω-continuous

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  is-ω-continuous-Poset :
    (type-Poset P → type-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-ω-continuous-Poset f =
    (x : hom-Poset ℕ-Poset P)
    (y :
      has-least-upper-bound-family-of-elements-Poset P
        ( map-hom-Poset ℕ-Poset P x)) →
    is-least-upper-bound-family-of-elements-Poset Q
      ( f ∘ map-hom-Poset ℕ-Poset P x)
      ( f (pr1 y))

  is-prop-is-ω-continuous-Poset :
    (f : type-Poset P → type-Poset Q) →
    is-prop (is-ω-continuous-Poset f)
  is-prop-is-ω-continuous-Poset f =
    is-prop-Π (is-prop-preserves-ω-supremum-Poset P Q f)

  is-ω-continuous-prop-Poset :
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-ω-continuous-prop-Poset f =
    ( is-ω-continuous-Poset f) ,
    ( is-prop-is-ω-continuous-Poset f)

  ω-continuous-hom-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  ω-continuous-hom-Poset =
    Σ (type-Poset P → type-Poset Q) (is-ω-continuous-Poset)

  map-ω-continuous-hom-Poset :
    ω-continuous-hom-Poset → type-Poset P → type-Poset Q
  map-ω-continuous-hom-Poset = pr1

  is-ω-continuous-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset) →
    is-ω-continuous-Poset (map-ω-continuous-hom-Poset f)
  is-ω-continuous-ω-continuous-hom-Poset = pr2

  sup-map-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset) →
    (x : hom-Poset ℕ-Poset P) →
    has-least-upper-bound-family-of-elements-Poset P
      ( map-hom-Poset ℕ-Poset P x) →
    has-least-upper-bound-family-of-elements-Poset Q
      ( map-ω-continuous-hom-Poset f ∘ map-hom-Poset ℕ-Poset P x)
  sup-map-ω-continuous-hom-Poset f x y =
    ( map-ω-continuous-hom-Poset f (pr1 y) ,
      is-ω-continuous-ω-continuous-hom-Poset f x y)
```

## Properties

### ω-Continuous maps preserve order

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  abstract
    preserves-order-is-ω-continuous-Poset :
      {f : type-Poset P → type-Poset Q} →
      is-ω-continuous-Poset P Q f →
      preserves-order-Poset P Q f
    preserves-order-is-ω-continuous-Poset {f} H x y p =
      pr2
        ( H ( hom-ind-ℕ-Poset P
              ( rec-ℕ x (λ _ _ → y))
              ( ind-ℕ p (λ _ _ → refl-leq-Poset P y)))
            ( y ,
              ( λ z →
                ( λ g → g 1) ,
                ( λ q → ind-ℕ (transitive-leq-Poset P x y z q p) (λ _ _ → q))))
            ( f y))
        ( refl-leq-Poset Q (f y))
        ( 0)

  hom-ω-continuous-hom-Poset :
    ω-continuous-hom-Poset P Q → hom-Poset P Q
  hom-ω-continuous-hom-Poset f =
    map-ω-continuous-hom-Poset P Q f ,
    preserves-order-is-ω-continuous-Poset
      ( is-ω-continuous-ω-continuous-hom-Poset P Q f)
```

### Homotopies of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-ω-continuous-hom-Poset :
    (f g : ω-continuous-hom-Poset P Q) → UU (l1 ⊔ l3)
  htpy-ω-continuous-hom-Poset f g =
    map-ω-continuous-hom-Poset P Q f ~ map-ω-continuous-hom-Poset P Q g

  refl-htpy-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset P Q) →
    htpy-ω-continuous-hom-Poset f f
  refl-htpy-ω-continuous-hom-Poset f = refl-htpy

  htpy-eq-ω-continuous-hom-Poset :
    (f g : ω-continuous-hom-Poset P Q) →
    f ＝ g →
    htpy-ω-continuous-hom-Poset f g
  htpy-eq-ω-continuous-hom-Poset f .f refl =
    refl-htpy-ω-continuous-hom-Poset f

  is-torsorial-htpy-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset P Q) →
    is-torsorial (htpy-ω-continuous-hom-Poset f)
  is-torsorial-htpy-ω-continuous-hom-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-ω-continuous-hom-Poset P Q f))
      ( is-prop-is-ω-continuous-Poset P Q)
      ( map-ω-continuous-hom-Poset P Q f)
      ( refl-htpy)
      ( is-ω-continuous-ω-continuous-hom-Poset P Q f)

  is-equiv-htpy-eq-ω-continuous-hom-Poset :
    (f g : ω-continuous-hom-Poset P Q) →
    is-equiv (htpy-eq-ω-continuous-hom-Poset f g)
  is-equiv-htpy-eq-ω-continuous-hom-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-ω-continuous-hom-Poset f)
      ( htpy-eq-ω-continuous-hom-Poset f)

  extensionality-ω-continuous-hom-Poset :
    (f g : ω-continuous-hom-Poset P Q) →
    (f ＝ g) ≃ htpy-ω-continuous-hom-Poset f g
  pr1 (extensionality-ω-continuous-hom-Poset f g) =
    htpy-eq-ω-continuous-hom-Poset f g
  pr2 (extensionality-ω-continuous-hom-Poset f g) =
    is-equiv-htpy-eq-ω-continuous-hom-Poset f g

  eq-htpy-ω-continuous-hom-Poset :
    (f g : ω-continuous-hom-Poset P Q) →
    htpy-ω-continuous-hom-Poset f g → f ＝ g
  eq-htpy-ω-continuous-hom-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-ω-continuous-hom-Poset f g)
```

### The identity ω-continuous map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-ω-continuous-id-hom-Poset :
    is-ω-continuous-Poset P P (id {A = type-Poset P})
  is-ω-continuous-id-hom-Poset x y = pr2 y

  id-ω-continuous-hom-Poset : ω-continuous-hom-Poset P P
  id-ω-continuous-hom-Poset = id , is-ω-continuous-id-hom-Poset
```

### Composing ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  is-ω-continuous-comp-ω-continuous-hom-Poset :
    (g : ω-continuous-hom-Poset Q R)
    (f : ω-continuous-hom-Poset P Q) →
    is-ω-continuous-Poset P R
      ( map-ω-continuous-hom-Poset Q R g ∘
        map-ω-continuous-hom-Poset P Q f)
  is-ω-continuous-comp-ω-continuous-hom-Poset g f c y =
    is-ω-continuous-ω-continuous-hom-Poset Q R g
      ( comp-hom-Poset ℕ-Poset P Q (hom-ω-continuous-hom-Poset P Q f) c)
      ( map-ω-continuous-hom-Poset P Q f (pr1 y) ,
        is-ω-continuous-ω-continuous-hom-Poset P Q f c y)

  comp-ω-continuous-hom-Poset :
    (g : ω-continuous-hom-Poset Q R)
    (f : ω-continuous-hom-Poset P Q) →
    ω-continuous-hom-Poset P R
  comp-ω-continuous-hom-Poset g f =
    map-ω-continuous-hom-Poset Q R g ∘
    map-ω-continuous-hom-Poset P Q f ,
    is-ω-continuous-comp-ω-continuous-hom-Poset g f
```

### Unit laws for composition of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset P Q) →
    ( comp-ω-continuous-hom-Poset P Q Q
      ( id-ω-continuous-hom-Poset Q)
      ( f)) ＝
    ( f)
  left-unit-law-comp-ω-continuous-hom-Poset f =
    eq-htpy-ω-continuous-hom-Poset P Q
      ( comp-ω-continuous-hom-Poset P Q Q
        ( id-ω-continuous-hom-Poset Q)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-ω-continuous-hom-Poset :
    (f : ω-continuous-hom-Poset P Q) →
    ( comp-ω-continuous-hom-Poset P P Q
      ( f)
      ( id-ω-continuous-hom-Poset P)) ＝
    ( f)
  right-unit-law-comp-ω-continuous-hom-Poset f =
    eq-htpy-ω-continuous-hom-Poset P Q
      ( comp-ω-continuous-hom-Poset P P Q
        ( f)
        ( id-ω-continuous-hom-Poset P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  (h : ω-continuous-hom-Poset R S)
  (g : ω-continuous-hom-Poset Q R)
  (f : ω-continuous-hom-Poset P Q)
  where

  associative-comp-ω-continuous-hom-Poset :
    comp-ω-continuous-hom-Poset P Q S
      ( comp-ω-continuous-hom-Poset Q R S h g)
      ( f) ＝
    comp-ω-continuous-hom-Poset P R S
      ( h)
      ( comp-ω-continuous-hom-Poset P Q R g f)
  associative-comp-ω-continuous-hom-Poset =
    eq-htpy-ω-continuous-hom-Poset P S
      ( comp-ω-continuous-hom-Poset P Q S
        ( comp-ω-continuous-hom-Poset Q R S h g)
        ( f))
      ( comp-ω-continuous-hom-Poset P R S
        ( h)
        ( comp-ω-continuous-hom-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-ω-continuous-hom-Poset :
    comp-ω-continuous-hom-Poset P Q S
      ( comp-ω-continuous-hom-Poset Q R S h g)
      ( f) ＝ⁱ
    comp-ω-continuous-hom-Poset P R S
      ( h)
      ( comp-ω-continuous-hom-Poset P Q R g f)
  involutive-eq-associative-comp-ω-continuous-hom-Poset =
    involutive-eq-eq associative-comp-ω-continuous-hom-Poset
```
