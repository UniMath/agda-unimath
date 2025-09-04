# `2`-element types

```agda
module univalent-combinatorics.2-element-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.connected-components-universes
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subuniverses
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.equivalences
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**`2`-element types** are types that are
[merely equivalent](foundation.mere-equivalences.md) to the
[standard 2-element type](univalent-combinatorics.standard-finite-types.md)
`Fin 2`.

## Definition

### The condition that a type has two elements

```agda
has-two-elements-Prop : {l : Level} → UU l → Prop l
has-two-elements-Prop X = has-cardinality-ℕ-Prop 2 X

has-two-elements : {l : Level} → UU l → UU l
has-two-elements X = type-Prop (has-two-elements-Prop X)

is-prop-has-two-elements : {l : Level} {X : UU l} → is-prop (has-two-elements X)
is-prop-has-two-elements {l} {X} = is-prop-type-Prop (has-two-elements-Prop X)
```

### The type of all `2`-element types of universe level `l`

```agda
2-Element-Type : (l : Level) → UU (lsuc l)
2-Element-Type l = Type-With-Cardinality-ℕ l 2

type-2-Element-Type : {l : Level} → 2-Element-Type l → UU l
type-2-Element-Type = pr1

has-two-elements-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → has-two-elements (type-2-Element-Type X)
has-two-elements-type-2-Element-Type = pr2

is-finite-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-finite (type-2-Element-Type X)
is-finite-type-2-Element-Type X =
  is-finite-has-cardinality-ℕ 2 (has-two-elements-type-2-Element-Type X)

finite-type-2-Element-Type : {l : Level} → 2-Element-Type l → Finite-Type l
pr1 (finite-type-2-Element-Type X) = type-2-Element-Type X
pr2 (finite-type-2-Element-Type X) = is-finite-type-2-Element-Type X

standard-2-Element-Type : (l : Level) → 2-Element-Type l
standard-2-Element-Type l = raise-Fin-Type-With-Cardinality-ℕ l 2

type-standard-2-Element-Type : (l : Level) → UU l
type-standard-2-Element-Type l = type-2-Element-Type (standard-2-Element-Type l)

zero-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
zero-standard-2-Element-Type = map-raise (zero-Fin 1)

one-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
one-standard-2-Element-Type = map-raise (one-Fin 1)
```

## Properties

### The condition of having two elements is closed under equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-two-elements-equiv : X ≃ Y → has-two-elements X → has-two-elements Y
  has-two-elements-equiv e H =
    transitive-mere-equiv (Fin 2) X Y (unit-trunc-Prop e) H

  has-two-elements-equiv' : X ≃ Y → has-two-elements Y → has-two-elements X
  has-two-elements-equiv' e H =
    transitive-mere-equiv (Fin 2) Y X (unit-trunc-Prop (inv-equiv e)) H
```

### Any `2`-element type is inhabited

```agda
is-inhabited-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → type-trunc-Prop (type-2-Element-Type X)
is-inhabited-2-Element-Type X =
  apply-universal-property-trunc-Prop
    ( has-two-elements-type-2-Element-Type X)
    ( trunc-Prop (type-2-Element-Type X))
    ( λ e → unit-trunc-Prop (map-equiv e (zero-Fin 1)))
```

### Any `2`-element type is a set

```agda
is-set-has-two-elements :
  {l : Level} {X : UU l} → has-two-elements X → is-set X
is-set-has-two-elements H = is-set-has-cardinality-ℕ 2 H

is-set-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-set (type-2-Element-Type X)
is-set-type-2-Element-Type X =
  is-set-has-cardinality-ℕ 2 (has-two-elements-type-2-Element-Type X)

set-2-Element-Type :
  {l : Level} → 2-Element-Type l → Set l
pr1 (set-2-Element-Type X) = type-2-Element-Type X
pr2 (set-2-Element-Type X) = is-set-type-2-Element-Type X
```

### Characterizing identifications between general `2`-element types

```agda
equiv-2-Element-Type :
  {l1 l2 : Level} → 2-Element-Type l1 → 2-Element-Type l2 → UU (l1 ⊔ l2)
equiv-2-Element-Type X Y = equiv-Type-With-Cardinality-ℕ 2 X Y

id-equiv-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) → equiv-2-Element-Type X X
id-equiv-2-Element-Type X = id-equiv

equiv-eq-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → X ＝ Y → equiv-2-Element-Type X Y
equiv-eq-2-Element-Type X Y = equiv-eq-component-UU-Level

abstract
  is-torsorial-equiv-2-Element-Type :
    {l1 : Level} (X : 2-Element-Type l1) →
    is-torsorial (λ (Y : 2-Element-Type l1) → equiv-2-Element-Type X Y)
  is-torsorial-equiv-2-Element-Type X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-2-Element-Type :
    {l1 : Level} (X Y : 2-Element-Type l1) →
    is-equiv (equiv-eq-2-Element-Type X Y)
  is-equiv-equiv-eq-2-Element-Type = is-equiv-equiv-eq-component-UU-Level

eq-equiv-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → equiv-2-Element-Type X Y → X ＝ Y
eq-equiv-2-Element-Type X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-2-Element-Type X Y)

extensionality-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → (X ＝ Y) ≃ equiv-2-Element-Type X Y
pr1 (extensionality-2-Element-Type X Y) = equiv-eq-2-Element-Type X Y
pr2 (extensionality-2-Element-Type X Y) = is-equiv-equiv-eq-2-Element-Type X Y
```

### Characterization the identifications of `Fin 2` with a `2`-element type `X`

#### Evaluating an equivalence and an automorphism at `0 : Fin 2`

```agda
ev-zero-equiv-Fin-2 :
  {l1 : Level} {X : UU l1} → (Fin 2 ≃ X) → X
ev-zero-equiv-Fin-2 e = map-equiv e (zero-Fin 1)

ev-zero-aut-Fin-2 : (Fin 2 ≃ Fin 2) → Fin 2
ev-zero-aut-Fin-2 = ev-zero-equiv-Fin-2
```

#### Evaluating an automorphism at `0 : Fin 2` is an equivalence

```agda
aut-point-Fin-2 :
  Fin 2 → (Fin 2 ≃ Fin 2)
aut-point-Fin-2 (inl (inr star)) = id-equiv
aut-point-Fin-2 (inr star) = equiv-succ-Fin 2

abstract
  is-section-aut-point-Fin-2 :
    (ev-zero-aut-Fin-2 ∘ aut-point-Fin-2) ~ id
  is-section-aut-point-Fin-2 (inl (inr star)) = refl
  is-section-aut-point-Fin-2 (inr star) = refl

  is-retraction-aut-point-Fin-2' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    map-equiv e (zero-Fin 1) ＝ x →
    map-equiv e (one-Fin 1) ＝ y → htpy-equiv (aut-point-Fin-2 x) e
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inl (inr star)) p q (inr star) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inr star) p q (inr star) = inv q
  is-retraction-aut-point-Fin-2' e
    (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inr star) (inl (inr star)) p q (inr star) = inv q
  is-retraction-aut-point-Fin-2' e
    (inr star) (inr star) p q (inl (inr star)) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))
  is-retraction-aut-point-Fin-2' e
    (inr star) (inr star) p q (inr star) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))

  is-retraction-aut-point-Fin-2 :
    (aut-point-Fin-2 ∘ ev-zero-aut-Fin-2) ~ id
  is-retraction-aut-point-Fin-2 e =
    eq-htpy-equiv
      ( is-retraction-aut-point-Fin-2' e
        ( map-equiv e (zero-Fin 1))
        ( map-equiv e (one-Fin 1))
        ( refl)
        ( refl))

abstract
  is-equiv-ev-zero-aut-Fin-2 : is-equiv ev-zero-aut-Fin-2
  is-equiv-ev-zero-aut-Fin-2 =
    is-equiv-is-invertible
      aut-point-Fin-2
      is-section-aut-point-Fin-2
      is-retraction-aut-point-Fin-2

equiv-ev-zero-aut-Fin-2 : (Fin 2 ≃ Fin 2) ≃ Fin 2
pr1 equiv-ev-zero-aut-Fin-2 = ev-zero-aut-Fin-2
pr2 equiv-ev-zero-aut-Fin-2 = is-equiv-ev-zero-aut-Fin-2
```

#### If `X` is a `2`-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where

  abstract
    is-equiv-ev-zero-equiv-Fin-2 :
      is-equiv (ev-zero-equiv-Fin-2 {l1} {type-2-Element-Type X})
    is-equiv-ev-zero-equiv-Fin-2 =
      apply-universal-property-trunc-Prop
        ( has-two-elements-type-2-Element-Type X)
        ( is-equiv-Prop (ev-zero-equiv-Fin-2))
        ( λ α →
          is-equiv-left-factor
            ( ev-zero-equiv-Fin-2)
            ( map-equiv (equiv-postcomp-equiv α (Fin 2)))
            ( is-equiv-comp
              ( map-equiv α)
              ( ev-zero-equiv-Fin-2)
              ( is-equiv-ev-zero-aut-Fin-2)
              ( is-equiv-map-equiv α))
            ( is-equiv-postcomp-equiv-equiv α))

  equiv-ev-zero-equiv-Fin-2 :
    (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
  pr1 equiv-ev-zero-equiv-Fin-2 = ev-zero-equiv-Fin-2
  pr2 equiv-ev-zero-equiv-Fin-2 = is-equiv-ev-zero-equiv-Fin-2

  equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 ≃ type-2-Element-Type X
  equiv-point-2-Element-Type =
    map-inv-equiv equiv-ev-zero-equiv-Fin-2

  map-equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 → type-2-Element-Type X
  map-equiv-point-2-Element-Type x = map-equiv (equiv-point-2-Element-Type x)

  map-inv-equiv-point-2-Element-Type :
    type-2-Element-Type X → type-2-Element-Type X → Fin 2
  map-inv-equiv-point-2-Element-Type x =
    map-inv-equiv (equiv-point-2-Element-Type x)

  is-section-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-equiv-point-2-Element-Type x ∘ map-inv-equiv-point-2-Element-Type x) ~
    id
  is-section-map-inv-equiv-point-2-Element-Type x =
    is-section-map-inv-equiv (equiv-point-2-Element-Type x)

  is-retraction-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-inv-equiv-point-2-Element-Type x ∘ map-equiv-point-2-Element-Type x) ~
    id
  is-retraction-map-inv-equiv-point-2-Element-Type x =
    is-retraction-map-inv-equiv (equiv-point-2-Element-Type x)

  compute-map-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    map-equiv-point-2-Element-Type x (zero-Fin 1) ＝ x
  compute-map-equiv-point-2-Element-Type =
    is-section-map-inv-equiv equiv-ev-zero-equiv-Fin-2

  is-unique-equiv-point-2-Element-Type :
    (e : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv (equiv-point-2-Element-Type (map-equiv e (zero-Fin 1))) e
  is-unique-equiv-point-2-Element-Type e =
    htpy-eq-equiv (is-retraction-map-inv-equiv equiv-ev-zero-equiv-Fin-2 e)
```

#### The type of pointed `2`-element types of any universe level is contractible

```agda
Pointed-2-Element-Type : (l : Level) → UU (lsuc l)
Pointed-2-Element-Type l = Σ (2-Element-Type l) type-2-Element-Type

abstract
  is-contr-pointed-2-Element-Type :
    {l : Level} → is-contr (Pointed-2-Element-Type l)
  is-contr-pointed-2-Element-Type {l} =
    is-contr-equiv'
      ( Σ ( 2-Element-Type l)
          ( equiv-2-Element-Type (standard-2-Element-Type l)))
      ( equiv-tot
        ( λ X →
          ( equiv-ev-zero-equiv-Fin-2 X) ∘e
          ( equiv-precomp-equiv (compute-raise-Fin l 2) (pr1 X))))
      ( is-torsorial-equiv-subuniverse
        ( has-cardinality-ℕ-Prop 2)
        ( standard-2-Element-Type l))
```

#### Completing the characterization of the identity type of the type of `2`-element types of arbitrary universe level

```agda
point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  standard-2-Element-Type l ＝ X → type-2-Element-Type X
point-eq-2-Element-Type refl = map-raise (zero-Fin 1)

abstract
  is-equiv-point-eq-2-Element-Type :
    {l : Level} (X : 2-Element-Type l) →
    is-equiv (point-eq-2-Element-Type {l} {X})
  is-equiv-point-eq-2-Element-Type {l} =
    fundamental-theorem-id
      ( is-contr-pointed-2-Element-Type)
      ( λ X → point-eq-2-Element-Type {l} {X})

equiv-point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  (standard-2-Element-Type l ＝ X) ≃ type-2-Element-Type X
pr1 (equiv-point-eq-2-Element-Type {l} {X}) =
  point-eq-2-Element-Type
pr2 (equiv-point-eq-2-Element-Type {l} {X}) =
  is-equiv-point-eq-2-Element-Type X

eq-point-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  type-2-Element-Type X → standard-2-Element-Type l ＝ X
eq-point-2-Element-Type =
  map-inv-equiv equiv-point-eq-2-Element-Type

is-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  is-identity-system (type-2-Element-Type {l1}) X x
is-identity-system-type-2-Element-Type X x =
  is-identity-system-is-torsorial X x (is-contr-pointed-2-Element-Type)

dependent-universal-property-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  dependent-universal-property-identity-system
    ( type-2-Element-Type {l1})
    { a = X}
    ( x)
dependent-universal-property-identity-system-type-2-Element-Type X x =
  dependent-universal-property-identity-system-is-torsorial x
    ( is-contr-pointed-2-Element-Type)
```

### For any `2`-element type `X`, the type of automorphisms on `X` is a `2`-element type

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  has-two-elements-Aut-2-Element-Type :
    has-two-elements (Aut (type-2-Element-Type X))
  has-two-elements-Aut-2-Element-Type =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-2-Element-Type X)
      ( has-two-elements-Prop (Aut (type-2-Element-Type X)))
      ( λ e →
        has-two-elements-equiv
          ( ( equiv-postcomp-equiv e (type-2-Element-Type X)) ∘e
            ( equiv-precomp-equiv (inv-equiv e) (Fin 2)))
          ( unit-trunc-Prop (inv-equiv equiv-ev-zero-aut-Fin-2)))

  Aut-2-Element-Type : 2-Element-Type l
  pr1 Aut-2-Element-Type = Aut (type-2-Element-Type X)
  pr2 Aut-2-Element-Type = has-two-elements-Aut-2-Element-Type
```

### Evaluating homotopies of equivalences `e, e' : Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where

  ev-zero-htpy-equiv-Fin-2 :
    (e e' : Fin 2 ≃ type-2-Element-Type X) → htpy-equiv e e' →
    map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1)
  ev-zero-htpy-equiv-Fin-2 e e' H = H (zero-Fin 1)

  equiv-ev-zero-htpy-equiv-Fin-2' :
    (e e' : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv e e' ≃ (map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1))
  equiv-ev-zero-htpy-equiv-Fin-2' e e' =
    ( equiv-ap (equiv-ev-zero-equiv-Fin-2 X) e e') ∘e
    ( inv-equiv (extensionality-equiv e e'))

  abstract
    is-equiv-ev-zero-htpy-equiv-Fin-2 :
      (e e' : Fin 2 ≃ type-2-Element-Type X) →
      is-equiv (ev-zero-htpy-equiv-Fin-2 e e')
    is-equiv-ev-zero-htpy-equiv-Fin-2 e =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr
          ( tot (ev-zero-htpy-equiv-Fin-2 e))
          ( is-torsorial-htpy-equiv e)
          ( is-contr-equiv
            ( fiber (ev-zero-equiv-Fin-2) (map-equiv e (zero-Fin 1)))
            ( equiv-tot
              ( λ e' →
                equiv-inv
                  ( map-equiv e (zero-Fin 1))
                  ( map-equiv e' (zero-Fin 1))))
            ( is-contr-map-is-equiv
              ( is-equiv-ev-zero-equiv-Fin-2 X)
              ( map-equiv e (zero-Fin 1)))))

  equiv-ev-zero-htpy-equiv-Fin-2 :
    (e e' : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv e e' ≃ (map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1))
  pr1 (equiv-ev-zero-htpy-equiv-Fin-2 e e') =
    ev-zero-htpy-equiv-Fin-2 e e'
  pr2 (equiv-ev-zero-htpy-equiv-Fin-2 e e') =
    is-equiv-ev-zero-htpy-equiv-Fin-2 e e'
```

### The canonical type family on the type of `2`-element types has no section

```agda
abstract
  no-section-type-2-Element-Type :
    {l : Level} → ¬ ((X : 2-Element-Type l) → type-2-Element-Type X)
  no-section-type-2-Element-Type {l} f =
    is-not-contractible-Fin 2
      ( Eq-eq-ℕ)
      ( is-contr-equiv
        ( standard-2-Element-Type l ＝ standard-2-Element-Type l)
        ( ( inv-equiv equiv-point-eq-2-Element-Type) ∘e
          ( compute-raise-Fin l 2))
        ( is-prop-is-contr
          ( pair
            ( standard-2-Element-Type l)
            ( λ X → eq-point-2-Element-Type (f X)))
          ( standard-2-Element-Type l)
          ( standard-2-Element-Type l)))
```

### There is no decidability procedure that proves that an arbitrary `2`-element type is decidable

```agda
abstract
  is-not-decidable-type-2-Element-Type :
    {l : Level} →
    ¬ ((X : 2-Element-Type l) → is-decidable (type-2-Element-Type X))
  is-not-decidable-type-2-Element-Type {l} d =
    no-section-type-2-Element-Type
      ( λ X →
        map-right-unit-law-coproduct-is-empty
          ( pr1 X)
          ( ¬ (pr1 X))
          ( apply-universal-property-trunc-Prop
            ( pr2 X)
            ( double-negation-type-Prop (pr1 X))
            ( λ e → intro-double-negation {l} (map-equiv e (zero-Fin 1))))
          ( d X))
```

### Any automorphism on `Fin 2` is an involution

```agda
cases-is-involution-aut-Fin-2 :
  (e : Fin 2 ≃ Fin 2) (x y z : Fin 2) →
  map-equiv e x ＝ y → map-equiv e y ＝ z →
  map-equiv (e ∘e e) x ＝ x
cases-is-involution-aut-Fin-2 e (inl (inr star)) (inl (inr star)) z p q =
  ap (map-equiv e) p ∙ p
cases-is-involution-aut-Fin-2 e
  (inl (inr star)) (inr star) (inl (inr star)) p q =
  ap (map-equiv e) p ∙ q
cases-is-involution-aut-Fin-2 e (inl (inr star)) (inr star) (inr star) p q =
  ex-falso (neq-inr-inl (is-injective-equiv e (q ∙ inv p)))
cases-is-involution-aut-Fin-2 e
  (inr star) (inl (inr star)) (inl (inr star)) p q =
  ex-falso (neq-inr-inl (is-injective-equiv e (p ∙ inv q)))
cases-is-involution-aut-Fin-2 e (inr star) (inl (inr star)) (inr star) p q =
  ap (map-equiv e) p ∙ q
cases-is-involution-aut-Fin-2 e (inr star) (inr star) z p q =
  ap (map-equiv e) p ∙ p

is-involution-aut-Fin-2 : (e : Fin 2 ≃ Fin 2) → is-involution-aut e
is-involution-aut-Fin-2 e x =
  cases-is-involution-aut-Fin-2 e x
    ( map-equiv e x)
    ( map-equiv (e ∘e e) x)
    ( refl)
    ( refl)

module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-involution-aut-2-element-type :
    (e : equiv-2-Element-Type X X) → is-involution-aut e
  is-involution-aut-2-element-type e x =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-2-Element-Type X)
      ( Id-Prop (set-2-Element-Type X) (map-equiv (e ∘e e) x) x)
      ( λ h →
        ( ap (map-equiv (e ∘e e)) (inv (is-section-map-inv-equiv h x))) ∙
        ( ( ap (map-equiv e) (inv (is-section-map-inv-equiv h _))) ∙
          ( inv (is-section-map-inv-equiv h _) ∙
            ( ( ap
                ( map-equiv h)
                ( is-involution-aut-Fin-2 (inv-equiv h ∘e (e ∘e h)) _)) ∙
              ( is-section-map-inv-equiv h x)))))
```

### The swapping equivalence on arbitrary `2`-element types

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  swap-2-Element-Type : equiv-2-Element-Type X X
  swap-2-Element-Type =
    ( equiv-ev-zero-equiv-Fin-2 X) ∘e
    ( ( equiv-precomp-equiv (equiv-succ-Fin 2) (type-2-Element-Type X)) ∘e
      ( inv-equiv (equiv-ev-zero-equiv-Fin-2 X)))

  map-swap-2-Element-Type : type-2-Element-Type X → type-2-Element-Type X
  map-swap-2-Element-Type = map-equiv swap-2-Element-Type

  compute-swap-2-Element-Type' :
    (x y : type-2-Element-Type X) → x ≠ y → (z : Fin 2) →
    map-inv-equiv-point-2-Element-Type X x y ＝ z →
    map-swap-2-Element-Type x ＝ y
  compute-swap-2-Element-Type' x y f (inl (inr star)) q =
    ex-falso
      ( f
        ( (inv (compute-map-equiv-point-2-Element-Type X x)) ∙
          ( ( ap (map-equiv-point-2-Element-Type X x) (inv q)) ∙
            ( is-section-map-inv-equiv-point-2-Element-Type X x y))))
  compute-swap-2-Element-Type' x y p (inr star) q =
    ( ap (map-equiv-point-2-Element-Type X x) (inv q)) ∙
    ( is-section-map-inv-equiv-point-2-Element-Type X x y)

  compute-swap-2-Element-Type :
    (x y : type-2-Element-Type X) → x ≠ y →
    map-swap-2-Element-Type x ＝ y
  compute-swap-2-Element-Type x y p =
    compute-swap-2-Element-Type' x y p
      ( map-inv-equiv-point-2-Element-Type X x y)
      ( refl)

  compute-map-equiv-point-2-Element-Type' :
    (x : type-2-Element-Type X) →
    map-equiv-point-2-Element-Type X x (one-Fin 1) ＝
    map-swap-2-Element-Type x
  compute-map-equiv-point-2-Element-Type' x = refl

compute-swap-Fin-2 :
  map-swap-2-Element-Type (Fin-Type-With-Cardinality-ℕ 2) ~ succ-Fin 2
compute-swap-Fin-2 (inl (inr star)) =
  compute-swap-2-Element-Type
    ( Fin-Type-With-Cardinality-ℕ 2)
    ( zero-Fin 1)
    ( one-Fin 1)
    ( neq-inl-inr)
compute-swap-Fin-2 (inr star) =
  compute-swap-2-Element-Type
    ( Fin-Type-With-Cardinality-ℕ 2)
    ( one-Fin 1)
    ( zero-Fin 1)
    ( neq-inr-inl)
```

### The swapping equivalence is not the identity equivalence

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin :
    equiv-precomp-equiv (equiv-succ-Fin 2) (type-2-Element-Type X) ≠ id-equiv
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin p' =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-2-Element-Type X)
      ( empty-Prop)
      ( λ f →
        neq-inr-inl
          ( is-injective-equiv f
            ( htpy-eq-equiv (htpy-eq-equiv p' f) (zero-Fin 1))))

  is-not-identity-swap-2-Element-Type : swap-2-Element-Type X ≠ id-equiv
  is-not-identity-swap-2-Element-Type p =
    is-not-identity-equiv-precomp-equiv-equiv-succ-Fin
      ( ( ( inv (left-unit-law-equiv equiv1)) ∙
          ( ap (λ x → x ∘e equiv1) (inv (left-inverse-law-equiv equiv2)))) ∙
        ( ( inv
            ( right-unit-law-equiv ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1))) ∙
          ( ( ap
              ( λ x → ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1) ∘e x)
              ( inv (left-inverse-law-equiv equiv2))) ∙
          ( ( ( eq-equiv-eq-map-equiv refl) ∙
              ( ap (λ x → inv-equiv equiv2 ∘e (x ∘e equiv2)) p)) ∙
            ( ( ap
                ( λ x → inv-equiv equiv2 ∘e x)
                ( left-unit-law-equiv equiv2)) ∙
              ( left-inverse-law-equiv equiv2))))))
    where
    equiv1 : (Fin 2 ≃ type-2-Element-Type X) ≃ (Fin 2 ≃ type-2-Element-Type X)
    equiv1 = equiv-precomp-equiv (equiv-succ-Fin 2) (type-2-Element-Type X)
    equiv2 : (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
    equiv2 = equiv-ev-zero-equiv-Fin-2 X
```

### The swapping equivalence has no fixpoints

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  has-no-fixed-points-swap-2-Element-Type :
    {x : type-2-Element-Type X} → map-equiv (swap-2-Element-Type X) x ≠ x
  has-no-fixed-points-swap-2-Element-Type {x} P =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-2-Element-Type X)
      ( empty-Prop)
      ( λ h →
        is-not-identity-swap-2-Element-Type X
          (eq-htpy-equiv
            (λ y →
              f
                ( inv-equiv h)
                ( y)
                ( map-inv-equiv h x)
                ( map-inv-equiv h y)
                ( map-inv-equiv h (map-equiv (swap-2-Element-Type X) y))
                ( refl)
                ( refl)
                ( refl))))
    where
    f :
      ( h : type-2-Element-Type X ≃ Fin 2)
      ( y : type-2-Element-Type X) →
      ( k1 k2 k3 : Fin 2) →
        map-equiv h x ＝ k1 → map-equiv h y ＝ k2 →
        map-equiv h (map-equiv (swap-2-Element-Type X) y) ＝ k3 →
        map-equiv (swap-2-Element-Type X) y ＝ y
    f h y (inl (inr star)) (inl (inr star)) k3 p q r =
      tr
        ( λ z → map-equiv (swap-2-Element-Type X) z ＝ z)
        ( is-injective-equiv h (p ∙ inv q))
        ( P)
    f h y (inl (inr star)) (inr star) (inl (inr star)) p q r =
      ex-falso
        ( neq-inl-inr
          ( inv p ∙ (ap (map-equiv h) (inv P) ∙
            ( ap
              ( map-equiv (h ∘e (swap-2-Element-Type X)))
              ( is-injective-equiv h (p ∙ inv r)) ∙
              ( ( ap
                  ( map-equiv h)
                  ( is-involution-aut-2-element-type X
                    ( swap-2-Element-Type X) y)) ∙
                ( q))))))
    f h y (inl (inr star)) (inr star) (inr star) p q r =
      ( is-injective-equiv h (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inl (inr star)) p q r =
      ( is-injective-equiv h (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inr star) p q r =
      ex-falso
        ( neq-inr-inl
          ( inv p ∙ (ap (map-equiv h) (inv P) ∙
            ( ap
              ( map-equiv (h ∘e (swap-2-Element-Type X)))
              ( is-injective-equiv h (p ∙ inv r)) ∙
              ( ( ap
                  ( map-equiv h)
                  ( is-involution-aut-2-element-type X
                    ( swap-2-Element-Type X)
                    ( y))) ∙
                ( q))))))
    f h y (inr star) (inr star) k3 p q r =
      tr
        ( λ z → map-equiv (swap-2-Element-Type X) z ＝ z)
        ( is-injective-equiv h (p ∙ inv q))
        ( P)
```

### Evaluating an automorphism at `0 : Fin 2` is a group homomorphism

```agda
preserves-add-aut-point-Fin-2 :
  (a b : Fin 2) →
  aut-point-Fin-2 (add-Fin 2 a b) ＝
  ( aut-point-Fin-2 a ∘e aut-point-Fin-2 b)
preserves-add-aut-point-Fin-2 (inl (inr star)) (inl (inr star)) =
  eq-equiv-eq-map-equiv refl
preserves-add-aut-point-Fin-2 (inl (inr star)) (inr star) =
  eq-equiv-eq-map-equiv refl
preserves-add-aut-point-Fin-2 (inr star) (inl (inr star)) =
  eq-equiv-eq-map-equiv refl
preserves-add-aut-point-Fin-2 (inr star) (inr star) =
  eq-htpy-equiv (λ x → inv (is-involution-aut-Fin-2 (equiv-succ-Fin 2) x))
```

### Any Σ-type over `Fin 2` is a coproduct

```agda
is-coproduct-Σ-Fin-2 :
  {l : Level} (P : Fin 2 → UU l) →
  Σ (Fin 2) P ≃ (P (zero-Fin 1) + P (one-Fin 1))
is-coproduct-Σ-Fin-2 P =
  ( equiv-coproduct
    ( left-unit-law-Σ-is-contr is-contr-Fin-1 (zero-Fin 0))
    ( left-unit-law-Σ (P ∘ inr))) ∘e
  ( right-distributive-Σ-coproduct P)
```

### For any equivalence `e : Fin 2 ≃ X`, any element of `X` is either `e 0` or it is `e 1`

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  abstract
    is-contr-decide-value-equiv-Fin-2 :
      (e : Fin 2 ≃ type-2-Element-Type X) (x : type-2-Element-Type X) →
      is-contr
        ( ( x ＝ map-equiv e (zero-Fin 1)) +
          ( x ＝ map-equiv e (one-Fin 1)))
    is-contr-decide-value-equiv-Fin-2 e x =
      is-contr-equiv'
        ( fiber (map-equiv e) x)
        ( ( is-coproduct-Σ-Fin-2 (λ y → x ＝ map-equiv e y)) ∘e
          ( equiv-tot (λ y → equiv-inv (map-equiv e y) x)))
        ( is-contr-map-is-equiv (is-equiv-map-equiv e) x)

  decide-value-equiv-Fin-2 :
    (e : Fin 2 ≃ type-2-Element-Type X) (x : type-2-Element-Type X) →
    (x ＝ map-equiv e (zero-Fin 1)) + (x ＝ map-equiv e (one-Fin 1))
  decide-value-equiv-Fin-2 e x =
    center (is-contr-decide-value-equiv-Fin-2 e x)
```

### There can't be three distinct elements in a `2`-element type

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  contradiction-3-distinct-element-2-Element-Type :
    (x y z : type-2-Element-Type X) →
    x ≠ y → y ≠ z → x ≠ z → empty
  contradiction-3-distinct-element-2-Element-Type x y z np nq nr =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-2-Element-Type X)
      ( empty-Prop)
      ( λ e →
        cases-contradiction-3-distinct-element-2-Element-Type
          ( e)
          ( decide-value-equiv-Fin-2 X e x)
          ( decide-value-equiv-Fin-2 X e y)
          ( decide-value-equiv-Fin-2 X e z))
    where
    cases-contradiction-3-distinct-element-2-Element-Type :
      (e : Fin 2 ≃ type-2-Element-Type X) →
      (x ＝ map-equiv e (zero-Fin 1)) + (x ＝ map-equiv e (one-Fin 1)) →
      (y ＝ map-equiv e (zero-Fin 1)) + (y ＝ map-equiv e (one-Fin 1)) →
      (z ＝ map-equiv e (zero-Fin 1)) + (z ＝ map-equiv e (one-Fin 1)) →
      empty
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inl refl) (inl refl) c3 = np refl
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inl refl) (inr refl) (inl refl) = nr refl
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inl refl) (inr refl) (inr refl) = nq refl
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inr refl) (inl refl) (inl refl) = nq refl
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inr refl) (inl refl) (inr refl) = nr refl
    cases-contradiction-3-distinct-element-2-Element-Type e
      (inr refl) (inr refl) c3 = np refl
```

### For any map between `2`-element types, being an equivalence is decidable

```agda
module _
  {l1 l2 : Level} (X : 2-Element-Type l1) (Y : 2-Element-Type l2)
  where

  is-decidable-is-equiv-2-Element-Type :
    (f : type-2-Element-Type X → type-2-Element-Type Y) →
    is-decidable (is-equiv f)
  is-decidable-is-equiv-2-Element-Type f =
    is-decidable-is-equiv-is-finite f
      ( is-finite-type-2-Element-Type X)
      ( is-finite-type-2-Element-Type Y)
```

### A map between `2`-element types is an equivalence if and only if its image is the full subtype of the codomain

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### A map between `2`-element types is not an equivalence if and only if its image is a singleton subtype of the codomain

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### Any map between `2`-element types that is not an equivalence is constant

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

```agda
{-
  is-constant-is-not-equiv-2-Element-Type :
    (f : type-2-Element-Type X → type-2-Element-Type Y) →
    ¬ (is-equiv f) →
    Σ (type-2-Element-Type Y) (λ y → f ~ const _ y)
  pr1 (is-constant-is-not-equiv-2-Element-Type f H) = {!!}
  pr2 (is-constant-is-not-equiv-2-Element-Type f H) = {!!}
  -}
```

### Any map between `2`-element types is either an equivalence or it is constant

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### Coinhabited `2`-element types are equivalent

```agda
{-
equiv-iff-2-Element-Type :
  {l1 l2 : Level} (X : 2-Element-Type l1) (Y : 2-Element-Type l2) →
  (type-2-Element-Type X ↔ type-2-Element-Type Y) →
  (equiv-2-Element-Type X Y)
equiv-iff-2-Element-Type X Y (f , g) = {!is-decidable-is-equiv-is-finite!}
-}
```
