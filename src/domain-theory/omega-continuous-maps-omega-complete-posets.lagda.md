# ω-Continuous maps between ω-complete posets

```agda
module domain-theory.omega-continuous-maps-omega-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets
open import domain-theory.omega-complete-posets
open import domain-theory.omega-continuous-maps-posets

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
[ω-complete posets](domain-theory.omega-complete-posets.md) is said to be
{{#concept "ω-continuous" Disambiguation="map of ω-complete posets" Agda=ω-continuous-hom-ω-Complete-Poset}}
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
  {l1 l2 l3 l4 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  (f : type-ω-Complete-Poset P → type-ω-Complete-Poset Q)
  (x : hom-Poset ℕ-Poset (poset-ω-Complete-Poset P))
  where

  preserves-ω-supremum-ω-Complete-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-ω-supremum-ω-Complete-Poset =
    (y :
      has-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset P)
        ( map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)) →
    is-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset Q)
      ( f ∘ map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)
      ( f (pr1 y))

  is-prop-preserves-ω-supremum-ω-Complete-Poset :
    is-prop preserves-ω-supremum-ω-Complete-Poset
  is-prop-preserves-ω-supremum-ω-Complete-Poset =
    is-prop-Π
      ( λ y →
        is-prop-is-least-upper-bound-family-of-elements-Poset
          ( poset-ω-Complete-Poset Q)
          ( f ∘ map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)
          ( f (pr1 y)))

  preserves-ω-supremum-prop-ω-Complete-Poset :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  preserves-ω-supremum-prop-ω-Complete-Poset =
    preserves-ω-supremum-ω-Complete-Poset ,
    is-prop-preserves-ω-supremum-ω-Complete-Poset
```

### The predicate on a map of ω-complete posets of being ω-continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  where

  is-ω-continuous-ω-Complete-Poset :
    (type-ω-Complete-Poset P → type-ω-Complete-Poset Q) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-ω-continuous-ω-Complete-Poset f =
    (x : hom-Poset ℕ-Poset (poset-ω-Complete-Poset P))
    (y :
      has-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset P)
        ( map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)) →
    is-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset Q)
      ( f ∘ map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)
      ( f (pr1 y))

  is-prop-is-ω-continuous-ω-Complete-Poset :
    (f : type-ω-Complete-Poset P → type-ω-Complete-Poset Q) →
    is-prop (is-ω-continuous-ω-Complete-Poset f)
  is-prop-is-ω-continuous-ω-Complete-Poset f =
    is-prop-Π (is-prop-preserves-ω-supremum-ω-Complete-Poset P Q f)

  is-ω-continuous-prop-ω-Complete-Poset :
    (type-ω-Complete-Poset P → type-ω-Complete-Poset Q) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-ω-continuous-prop-ω-Complete-Poset f =
    ( is-ω-continuous-ω-Complete-Poset f) ,
    ( is-prop-is-ω-continuous-ω-Complete-Poset f)

  ω-continuous-hom-ω-Complete-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  ω-continuous-hom-ω-Complete-Poset =
    ω-continuous-hom-Poset (poset-ω-Complete-Poset P) (poset-ω-Complete-Poset Q)

  map-ω-continuous-hom-ω-Complete-Poset :
    ω-continuous-hom-ω-Complete-Poset →
    type-ω-Complete-Poset P →
    type-ω-Complete-Poset Q
  map-ω-continuous-hom-ω-Complete-Poset = pr1

  is-ω-continuous-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset) →
    is-ω-continuous-ω-Complete-Poset (map-ω-continuous-hom-ω-Complete-Poset f)
  is-ω-continuous-ω-continuous-hom-ω-Complete-Poset = pr2

  sup-map-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset) →
    (x : hom-Poset ℕ-Poset (poset-ω-Complete-Poset P)) →
    has-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset P)
      ( map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x) →
    has-least-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset Q)
      ( map-ω-continuous-hom-ω-Complete-Poset f ∘
        map-hom-Poset ℕ-Poset (poset-ω-Complete-Poset P) x)
  sup-map-ω-continuous-hom-ω-Complete-Poset f x y =
    ( map-ω-continuous-hom-ω-Complete-Poset f (pr1 y) ,
      is-ω-continuous-ω-continuous-hom-ω-Complete-Poset f x y)
```

## Properties

### ω-Continuous maps preserve order

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  where

  abstract
    preserves-order-is-ω-continuous-ω-Complete-Poset :
      {f : type-ω-Complete-Poset P → type-ω-Complete-Poset Q} →
      is-ω-continuous-ω-Complete-Poset P Q f →
      preserves-order-Poset
        ( poset-ω-Complete-Poset P)
        ( poset-ω-Complete-Poset Q) f
    preserves-order-is-ω-continuous-ω-Complete-Poset {f} H x y p =
      pr2
        ( H ( hom-ind-ℕ-Poset (poset-ω-Complete-Poset P)
              ( rec-ℕ x (λ _ _ → y))
              ( ind-ℕ p (λ _ _ → refl-leq-ω-Complete-Poset P y)))
            ( y ,
              ( λ z →
                ( λ g → g 1) ,
                ( λ q →
                  ind-ℕ
                    ( transitive-leq-ω-Complete-Poset P x y z q p)
                    ( λ _ _ → q))))
            ( f y))
        ( refl-leq-ω-Complete-Poset Q (f y))
        ( 0)

  hom-ω-continuous-hom-ω-Complete-Poset :
    ω-continuous-hom-ω-Complete-Poset P Q →
    hom-Poset (poset-ω-Complete-Poset P) (poset-ω-Complete-Poset Q)
  hom-ω-continuous-hom-ω-Complete-Poset f =
    map-ω-continuous-hom-ω-Complete-Poset P Q f ,
    preserves-order-is-ω-continuous-ω-Complete-Poset
      ( is-ω-continuous-ω-continuous-hom-ω-Complete-Poset P Q f)
```

### Homotopies of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  where

  htpy-ω-continuous-hom-ω-Complete-Poset :
    (f g : ω-continuous-hom-ω-Complete-Poset P Q) → UU (l1 ⊔ l3)
  htpy-ω-continuous-hom-ω-Complete-Poset f g =
    map-ω-continuous-hom-ω-Complete-Poset P Q f ~
    map-ω-continuous-hom-ω-Complete-Poset P Q g

  refl-htpy-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    htpy-ω-continuous-hom-ω-Complete-Poset f f
  refl-htpy-ω-continuous-hom-ω-Complete-Poset f = refl-htpy

  htpy-eq-ω-continuous-hom-ω-Complete-Poset :
    (f g : ω-continuous-hom-ω-Complete-Poset P Q) →
    f ＝ g →
    htpy-ω-continuous-hom-ω-Complete-Poset f g
  htpy-eq-ω-continuous-hom-ω-Complete-Poset f .f refl =
    refl-htpy-ω-continuous-hom-ω-Complete-Poset f

  is-torsorial-htpy-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    is-torsorial (htpy-ω-continuous-hom-ω-Complete-Poset f)
  is-torsorial-htpy-ω-continuous-hom-ω-Complete-Poset f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-ω-continuous-hom-ω-Complete-Poset P Q f))
      ( is-prop-is-ω-continuous-ω-Complete-Poset P Q)
      ( map-ω-continuous-hom-ω-Complete-Poset P Q f)
      ( refl-htpy)
      ( is-ω-continuous-ω-continuous-hom-ω-Complete-Poset P Q f)

  is-equiv-htpy-eq-ω-continuous-hom-ω-Complete-Poset :
    (f g : ω-continuous-hom-ω-Complete-Poset P Q) →
    is-equiv (htpy-eq-ω-continuous-hom-ω-Complete-Poset f g)
  is-equiv-htpy-eq-ω-continuous-hom-ω-Complete-Poset f =
    fundamental-theorem-id
      ( is-torsorial-htpy-ω-continuous-hom-ω-Complete-Poset f)
      ( htpy-eq-ω-continuous-hom-ω-Complete-Poset f)

  extensionality-ω-continuous-hom-ω-Complete-Poset :
    (f g : ω-continuous-hom-ω-Complete-Poset P Q) →
    (f ＝ g) ≃ htpy-ω-continuous-hom-ω-Complete-Poset f g
  pr1 (extensionality-ω-continuous-hom-ω-Complete-Poset f g) =
    htpy-eq-ω-continuous-hom-ω-Complete-Poset f g
  pr2 (extensionality-ω-continuous-hom-ω-Complete-Poset f g) =
    is-equiv-htpy-eq-ω-continuous-hom-ω-Complete-Poset f g

  eq-htpy-ω-continuous-hom-ω-Complete-Poset :
    (f g : ω-continuous-hom-ω-Complete-Poset P Q) →
    htpy-ω-continuous-hom-ω-Complete-Poset f g → f ＝ g
  eq-htpy-ω-continuous-hom-ω-Complete-Poset f g =
    map-inv-is-equiv (is-equiv-htpy-eq-ω-continuous-hom-ω-Complete-Poset f g)
```

### The identity ω-continuous map

```agda
module _
  {l1 l2 : Level} (P : ω-Complete-Poset l1 l2)
  where

  is-ω-continuous-id-ω-Complete-Poset :
    is-ω-continuous-ω-Complete-Poset P P (id {A = type-ω-Complete-Poset P})
  is-ω-continuous-id-ω-Complete-Poset x y = pr2 y

  id-ω-continuous-hom-ω-Complete-Poset : ω-continuous-hom-ω-Complete-Poset P P
  id-ω-continuous-hom-ω-Complete-Poset =
    id , is-ω-continuous-id-ω-Complete-Poset
```

### Composing ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : ω-Complete-Poset l1 l2)
  (Q : ω-Complete-Poset l3 l4)
  (R : ω-Complete-Poset l5 l6)
  where

  is-ω-continuous-comp-ω-continuous-hom-ω-Complete-Poset :
    (g : ω-continuous-hom-ω-Complete-Poset Q R)
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    is-ω-continuous-ω-Complete-Poset P R
      ( map-ω-continuous-hom-ω-Complete-Poset Q R g ∘
        map-ω-continuous-hom-ω-Complete-Poset P Q f)
  is-ω-continuous-comp-ω-continuous-hom-ω-Complete-Poset g f c y =
    is-ω-continuous-ω-continuous-hom-ω-Complete-Poset Q R g
      ( comp-hom-Poset ℕ-Poset
        ( poset-ω-Complete-Poset P)
        ( poset-ω-Complete-Poset Q)
        ( hom-ω-continuous-hom-ω-Complete-Poset P Q f) c)
      ( map-ω-continuous-hom-ω-Complete-Poset P Q f (pr1 y) ,
        is-ω-continuous-ω-continuous-hom-ω-Complete-Poset P Q f c y)

  comp-ω-continuous-hom-ω-Complete-Poset :
    (g : ω-continuous-hom-ω-Complete-Poset Q R)
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    ω-continuous-hom-ω-Complete-Poset P R
  comp-ω-continuous-hom-ω-Complete-Poset g f =
    map-ω-continuous-hom-ω-Complete-Poset Q R g ∘
    map-ω-continuous-hom-ω-Complete-Poset P Q f ,
    is-ω-continuous-comp-ω-continuous-hom-ω-Complete-Poset g f
```

### Unit laws for composition of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  where

  left-unit-law-comp-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    ( comp-ω-continuous-hom-ω-Complete-Poset P Q Q
      ( id-ω-continuous-hom-ω-Complete-Poset Q)
      ( f)) ＝
    ( f)
  left-unit-law-comp-ω-continuous-hom-ω-Complete-Poset f =
    eq-htpy-ω-continuous-hom-ω-Complete-Poset P Q
      ( comp-ω-continuous-hom-ω-Complete-Poset P Q Q
        ( id-ω-continuous-hom-ω-Complete-Poset Q)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-ω-continuous-hom-ω-Complete-Poset :
    (f : ω-continuous-hom-ω-Complete-Poset P Q) →
    ( comp-ω-continuous-hom-ω-Complete-Poset P P Q
      ( f)
      ( id-ω-continuous-hom-ω-Complete-Poset P)) ＝
    ( f)
  right-unit-law-comp-ω-continuous-hom-ω-Complete-Poset f =
    eq-htpy-ω-continuous-hom-ω-Complete-Poset P Q
      ( comp-ω-continuous-hom-ω-Complete-Poset P P Q
        ( f)
        ( id-ω-continuous-hom-ω-Complete-Poset P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of ω-continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : ω-Complete-Poset l1 l2) (Q : ω-Complete-Poset l3 l4)
  (R : ω-Complete-Poset l5 l6) (S : ω-Complete-Poset l7 l8)
  (h : ω-continuous-hom-ω-Complete-Poset R S)
  (g : ω-continuous-hom-ω-Complete-Poset Q R)
  (f : ω-continuous-hom-ω-Complete-Poset P Q)
  where

  associative-comp-ω-continuous-hom-ω-Complete-Poset :
    comp-ω-continuous-hom-ω-Complete-Poset P Q S
      ( comp-ω-continuous-hom-ω-Complete-Poset Q R S h g)
      ( f) ＝
    comp-ω-continuous-hom-ω-Complete-Poset P R S
      ( h)
      ( comp-ω-continuous-hom-ω-Complete-Poset P Q R g f)
  associative-comp-ω-continuous-hom-ω-Complete-Poset =
    eq-htpy-ω-continuous-hom-ω-Complete-Poset P S
      ( comp-ω-continuous-hom-ω-Complete-Poset P Q S
        ( comp-ω-continuous-hom-ω-Complete-Poset Q R S h g)
        ( f))
      ( comp-ω-continuous-hom-ω-Complete-Poset P R S
        ( h)
        ( comp-ω-continuous-hom-ω-Complete-Poset P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-ω-continuous-hom-ω-Complete-Poset :
    comp-ω-continuous-hom-ω-Complete-Poset P Q S
      ( comp-ω-continuous-hom-ω-Complete-Poset Q R S h g)
      ( f) ＝ⁱ
    comp-ω-continuous-hom-ω-Complete-Poset P R S
      ( h)
      ( comp-ω-continuous-hom-ω-Complete-Poset P Q R g f)
  involutive-eq-associative-comp-ω-continuous-hom-ω-Complete-Poset =
    involutive-eq-eq associative-comp-ω-continuous-hom-ω-Complete-Poset
```
