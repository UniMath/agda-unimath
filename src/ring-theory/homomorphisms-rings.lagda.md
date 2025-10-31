# Homomorphisms of rings

```agda
module ring-theory.homomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

{{#concept "Ring homomorphisms" WD="ring homomorphism" WDID=Q1194212 Agda=hom-Ring}}
are maps between [rings](ring-theory.rings.md) that preserve the ring structure.

## Definitions

### The predicate on group homomorphisms between rings of preserving multiplication

```agda
preserves-mul-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  hom-Ab (ab-Ring R) (ab-Ring S) → UU (l1 ⊔ l2)
preserves-mul-hom-Ab R S f =
  {x y : type-Ring R} →
  map-hom-Ab (ab-Ring R) (ab-Ring S) f (mul-Ring R x y) ＝
  mul-Ring S
    ( map-hom-Ab (ab-Ring R) (ab-Ring S) f x)
    ( map-hom-Ab (ab-Ring R) (ab-Ring S) f y)

is-prop-preserves-mul-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : hom-Ab (ab-Ring R) (ab-Ring S)) →
  is-prop (preserves-mul-hom-Ab R S f)
is-prop-preserves-mul-hom-Ab R S f =
  is-prop-implicit-Π
    ( λ x →
      is-prop-implicit-Π
        ( λ y →
          is-set-type-Ring S
            ( map-hom-Ab (ab-Ring R) (ab-Ring S) f (mul-Ring R x y))
            ( mul-Ring S
              ( map-hom-Ab (ab-Ring R) (ab-Ring S) f x)
              ( map-hom-Ab (ab-Ring R) (ab-Ring S) f y))))
```

### The predicate on group homomorphisms between rings of preserving the unit

```agda
preserves-unit-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  hom-Ab (ab-Ring R) (ab-Ring S) → UU l2
preserves-unit-hom-Ab R S f =
  map-hom-Ab (ab-Ring R) (ab-Ring S) f (one-Ring R) ＝ one-Ring S

is-prop-preserves-unit-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : hom-Ab (ab-Ring R) (ab-Ring S)) →
  is-prop (preserves-unit-hom-Ab R S f)
is-prop-preserves-unit-hom-Ab R S f =
  is-set-type-Ring S
    ( map-hom-Ab (ab-Ring R) (ab-Ring S) f (one-Ring R))
    ( one-Ring S)
```

### The predicate of being a ring homomorphism

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  is-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Ring R) (ab-Ring S) → Prop (l1 ⊔ l2)
  is-ring-homomorphism-hom-Ab-Prop f =
    is-homomorphism-semiring-prop-hom-Commutative-Monoid
      ( semiring-Ring R)
      ( semiring-Ring S)
      ( hom-commutative-monoid-hom-Ab (ab-Ring R) (ab-Ring S) f)

  is-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Ring R) (ab-Ring S) → UU (l1 ⊔ l2)
  is-ring-homomorphism-hom-Ab f =
    type-Prop (is-ring-homomorphism-hom-Ab-Prop f)

  is-prop-is-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
    is-prop (is-ring-homomorphism-hom-Ab f)
  is-prop-is-ring-homomorphism-hom-Ab f =
    is-prop-type-Prop (is-ring-homomorphism-hom-Ab-Prop f)
```

### Ring homomorphisms

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  hom-set-Ring : Set (l1 ⊔ l2)
  hom-set-Ring =
    set-subset
      ( hom-set-Ab (ab-Ring R) (ab-Ring S))
      ( is-ring-homomorphism-hom-Ab-Prop R S)

  hom-Ring : UU (l1 ⊔ l2)
  hom-Ring = type-Set hom-set-Ring

  is-set-hom-Ring : is-set hom-Ring
  is-set-hom-Ring = is-set-type-Set hom-set-Ring

  module _
    (f : hom-Ring)
    where

    hom-ab-hom-Ring : hom-Ab (ab-Ring R) (ab-Ring S)
    hom-ab-hom-Ring = pr1 f

    hom-group-hom-Ring : hom-Group (group-Ring R) (group-Ring S)
    hom-group-hom-Ring = hom-ab-hom-Ring

    hom-commutative-monoid-hom-Ring :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Ring R)
        ( additive-commutative-monoid-Ring S)
    hom-commutative-monoid-hom-Ring =
      hom-commutative-monoid-hom-Ab (ab-Ring R) (ab-Ring S) hom-ab-hom-Ring

    map-hom-Ring : type-Ring R → type-Ring S
    map-hom-Ring = map-hom-Ab (ab-Ring R) (ab-Ring S) hom-ab-hom-Ring

    preserves-add-hom-Ring :
      preserves-add-Ab (ab-Ring R) (ab-Ring S) map-hom-Ring
    preserves-add-hom-Ring =
      preserves-add-hom-Ab (ab-Ring R) (ab-Ring S) hom-ab-hom-Ring

    preserves-zero-hom-Ring :
      preserves-zero-Ab (ab-Ring R) (ab-Ring S) map-hom-Ring
    preserves-zero-hom-Ring =
      preserves-zero-hom-Ab (ab-Ring R) (ab-Ring S) hom-ab-hom-Ring

    preserves-neg-hom-Ring :
      preserves-negatives-Ab (ab-Ring R) (ab-Ring S) map-hom-Ring
    preserves-neg-hom-Ring =
      preserves-negatives-hom-Ab (ab-Ring R) (ab-Ring S) hom-ab-hom-Ring

    preserves-mul-hom-Ring : preserves-mul-hom-Ab R S hom-ab-hom-Ring
    preserves-mul-hom-Ring = pr1 (pr2 f)

    preserves-one-hom-Ring : preserves-unit-hom-Ab R S hom-ab-hom-Ring
    preserves-one-hom-Ring = pr2 (pr2 f)

    is-ring-homomorphism-hom-Ring :
      is-ring-homomorphism-hom-Ab R S hom-ab-hom-Ring
    pr1 is-ring-homomorphism-hom-Ring = preserves-mul-hom-Ring
    pr2 is-ring-homomorphism-hom-Ring = preserves-one-hom-Ring

    hom-multiplicative-monoid-hom-Ring :
      hom-Monoid
        ( multiplicative-monoid-Ring R)
        ( multiplicative-monoid-Ring S)
    pr1 (pr1 hom-multiplicative-monoid-hom-Ring) = map-hom-Ring
    pr2 (pr1 hom-multiplicative-monoid-hom-Ring) = preserves-mul-hom-Ring
    pr2 hom-multiplicative-monoid-hom-Ring = preserves-one-hom-Ring

    hom-semiring-hom-Ring :
      hom-Semiring (semiring-Ring R) (semiring-Ring S)
    pr1 hom-semiring-hom-Ring = hom-commutative-monoid-hom-Ring
    pr2 hom-semiring-hom-Ring = is-ring-homomorphism-hom-Ring
```

### The identity ring homomorphism

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-mul-id-hom-Ring : preserves-mul-hom-Ab R R (id-hom-Ab (ab-Ring R))
  preserves-mul-id-hom-Ring = refl

  preserves-unit-id-hom-Ring : preserves-unit-hom-Ab R R (id-hom-Ab (ab-Ring R))
  preserves-unit-id-hom-Ring = refl

  is-ring-homomorphism-id-hom-Ring :
    is-ring-homomorphism-hom-Ab R R (id-hom-Ab (ab-Ring R))
  pr1 is-ring-homomorphism-id-hom-Ring = preserves-mul-id-hom-Ring
  pr2 is-ring-homomorphism-id-hom-Ring = preserves-unit-id-hom-Ring

  id-hom-Ring : hom-Ring R R
  pr1 id-hom-Ring = id-hom-Ab (ab-Ring R)
  pr2 id-hom-Ring = is-ring-homomorphism-id-hom-Ring
```

### Composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (g : hom-Ring S T) (f : hom-Ring R S)
  where

  hom-ab-comp-hom-Ring : hom-Ab (ab-Ring R) (ab-Ring T)
  hom-ab-comp-hom-Ring =
    comp-hom-Ab
      ( ab-Ring R)
      ( ab-Ring S)
      ( ab-Ring T)
      ( hom-ab-hom-Ring S T g)
      ( hom-ab-hom-Ring R S f)

  hom-multiplicative-monoid-comp-hom-Ring :
    hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring T)
  hom-multiplicative-monoid-comp-hom-Ring =
    comp-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( multiplicative-monoid-Ring T)
      ( hom-multiplicative-monoid-hom-Ring S T g)
      ( hom-multiplicative-monoid-hom-Ring R S f)

  preserves-mul-comp-hom-Ring : preserves-mul-hom-Ab R T hom-ab-comp-hom-Ring
  preserves-mul-comp-hom-Ring =
    preserves-mul-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring T)
      ( hom-multiplicative-monoid-comp-hom-Ring)

  preserves-unit-comp-hom-Ring :
    preserves-unit-hom-Ab R T hom-ab-comp-hom-Ring
  preserves-unit-comp-hom-Ring =
    preserves-unit-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring T)
      ( hom-multiplicative-monoid-comp-hom-Ring)

  is-ring-homomorphism-comp-hom-Ring :
    is-ring-homomorphism-hom-Ab R T hom-ab-comp-hom-Ring
  pr1 is-ring-homomorphism-comp-hom-Ring = preserves-mul-comp-hom-Ring
  pr2 is-ring-homomorphism-comp-hom-Ring = preserves-unit-comp-hom-Ring

  comp-hom-Ring : hom-Ring R T
  pr1 comp-hom-Ring = hom-ab-comp-hom-Ring
  pr2 comp-hom-Ring = is-ring-homomorphism-comp-hom-Ring
```

### Homotopies of ring homomorphisms

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  htpy-hom-Ring : hom-Ring R S → hom-Ring R S → UU (l1 ⊔ l2)
  htpy-hom-Ring f g = map-hom-Ring R S f ~ map-hom-Ring R S g

  refl-htpy-hom-Ring : (f : hom-Ring R S) → htpy-hom-Ring f f
  refl-htpy-hom-Ring f = refl-htpy
```

### Evaluating ring homomorphisms at an element

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  ev-element-hom-Ring : type-Ring R → hom-Ring R S → type-Ring S
  ev-element-hom-Ring x f = map-hom-Ring R S f x
```

## Properties

### Homotopies characterize identifications of ring homomorphisms

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  htpy-eq-hom-Ring :
    (g : hom-Ring R S) → (f ＝ g) → htpy-hom-Ring R S f g
  htpy-eq-hom-Ring .f refl = refl-htpy-hom-Ring R S f

  is-torsorial-htpy-hom-Ring :
    is-torsorial (htpy-hom-Ring R S f)
  is-torsorial-htpy-hom-Ring =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy-hom-Ab
        ( ab-Ring R)
        ( ab-Ring S)
        ( hom-ab-hom-Ring R S f))
      ( is-prop-is-ring-homomorphism-hom-Ab R S)
      ( hom-ab-hom-Ring R S f)
      ( refl-htpy-hom-Ring R S f)
      ( is-ring-homomorphism-hom-Ring R S f)

  is-equiv-htpy-eq-hom-Ring :
    (g : hom-Ring R S) → is-equiv (htpy-eq-hom-Ring g)
  is-equiv-htpy-eq-hom-Ring =
    fundamental-theorem-id
      is-torsorial-htpy-hom-Ring
      htpy-eq-hom-Ring

  extensionality-hom-Ring :
    (g : hom-Ring R S) → (f ＝ g) ≃ htpy-hom-Ring R S f g
  pr1 (extensionality-hom-Ring g) = htpy-eq-hom-Ring g
  pr2 (extensionality-hom-Ring g) = is-equiv-htpy-eq-hom-Ring g

  eq-htpy-hom-Ring :
    (g : hom-Ring R S) → htpy-hom-Ring R S f g → f ＝ g
  eq-htpy-hom-Ring g = map-inv-is-equiv (is-equiv-htpy-eq-hom-Ring g)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( R : Ring l1) (S : Ring l2) (T : Ring l3) (U : Ring l4)
  ( h : hom-Ring T U)
  ( g : hom-Ring S T)
  ( f : hom-Ring R S)
  where

  associative-comp-hom-Ring :
    comp-hom-Ring R S U (comp-hom-Ring S T U h g) f ＝
    comp-hom-Ring R T U h (comp-hom-Ring R S T g f)
  associative-comp-hom-Ring =
    eq-htpy-hom-Ring R U
      ( comp-hom-Ring R S U (comp-hom-Ring S T U h g) f)
      ( comp-hom-Ring R T U h (comp-hom-Ring R S T g f))
      ( refl-htpy)
```

### Unit laws for composition of ring homomorphisms

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  left-unit-law-comp-hom-Ring : comp-hom-Ring R S S (id-hom-Ring S) f ＝ f
  left-unit-law-comp-hom-Ring =
    eq-htpy-hom-Ring R S
      ( comp-hom-Ring R S S (id-hom-Ring S) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-Ring : comp-hom-Ring R R S f (id-hom-Ring R) ＝ f
  right-unit-law-comp-hom-Ring =
    eq-htpy-hom-Ring R S
      ( comp-hom-Ring R R S f (id-hom-Ring R))
      ( f)
      ( refl-htpy)
```

### The underlying morphism of abelian groups of the identity ring homomorphism is the identity homomorphism of abelian groups

```agda
id-law-ab-Ring :
  { l1 : Level} (R : Ring l1) →
  hom-ab-hom-Ring R R (id-hom-Ring R) ＝ id-hom-Ab (ab-Ring R)
id-law-ab-Ring R =
  eq-htpy-hom-Ab
    ( ab-Ring R)
    ( ab-Ring R)
    ( refl-htpy)
```

### The underlying morphism of abelian groups of a composition of ring homomorphisms is a composition of homomorphisms of abelian groups

```agda
comp-law-ab-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : hom-Ring S T) (f : hom-Ring R S) →
  hom-ab-hom-Ring R T (comp-hom-Ring R S T g f) ＝
  comp-hom-Ab
    ( ab-Ring R)
    ( ab-Ring S)
    ( ab-Ring T)
    ( hom-ab-hom-Ring S T g)
    ( hom-ab-hom-Ring R S f)
comp-law-ab-Ring R S T g f =
  eq-htpy-hom-Ab
    ( ab-Ring R)
    ( ab-Ring T)
    ( refl-htpy)
```

### Any ring homomorphism preserves invertible elements

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  (f : hom-Ring R S)
  where

  preserves-invertible-elements-hom-Ring :
    {x : type-Ring R} →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring S (map-hom-Ring R S f x)
  preserves-invertible-elements-hom-Ring =
    preserves-invertible-elements-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)
```
