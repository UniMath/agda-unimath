# Large submonoids

```agda
module group-theory.large-submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-large-monoids
open import group-theory.large-monoids
open import group-theory.large-subsemigroups
open import group-theory.monoids
open import group-theory.submonoids
open import group-theory.subsets-large-monoids
```

</details>

## Idea

A
{{#concept "submonoid" Disambiguation="of a large monoid" Agda=Large-Submonoid}}
of a [large monoid](group-theory.large-monoids.md) `M` is a
[subset](group-theory.subsets-large-monoids.md) of `M` that is closed under
multiplication and contains the unit.

## Definition

```agda
record
  Large-Submonoid
    {α : Level → Level}
    {β : Level → Level → Level}
    (γ : Level → Level)
    (M : Large-Monoid α β) :
    UUω
  where

  constructor
    make-Large-Submonoid

  field
    large-subsemigroup-Large-Submonoid :
      Large-Subsemigroup γ (large-semigroup-Large-Monoid M)

    contains-unit-Large-Submonoid :
      is-in-Large-Subsemigroup
        ( large-subsemigroup-Large-Submonoid)
        ( unit-Large-Monoid M)

  type-Large-Submonoid : (l : Level) → UU (α l ⊔ γ l)
  type-Large-Submonoid =
    type-Large-Subsemigroup large-subsemigroup-Large-Submonoid

  is-in-Large-Submonoid :
    {l : Level} → type-Large-Monoid M l → UU (γ l)
  is-in-Large-Submonoid =
    is-in-Large-Subsemigroup large-subsemigroup-Large-Submonoid

  prop-is-in-Large-Submonoid :
    {l : Level} → type-Large-Monoid M l → Prop (γ l)
  prop-is-in-Large-Submonoid =
    prop-is-in-Large-Subsemigroup large-subsemigroup-Large-Submonoid

  inclusion-Large-Submonoid :
    {l : Level} → type-Large-Submonoid l → type-Large-Monoid M l
  inclusion-Large-Submonoid = pr1

  subset-Large-Submonoid : subset-Large-Monoid γ M
  subset-Large-Submonoid =
    subset-Large-Subsemigroup large-subsemigroup-Large-Submonoid

  is-closed-under-mul-subset-Large-Submonoid :
    is-closed-under-mul-subset-Large-Monoid M subset-Large-Submonoid
  is-closed-under-mul-subset-Large-Submonoid =
    is-closed-under-mul-subset-Large-Subsemigroup
      ( large-subsemigroup-Large-Submonoid)

  is-closed-under-raise-subset-Large-Submonoid :
    {l1 : Level} (l2 : Level) (x : type-Large-Monoid M l1) →
    is-in-Large-Submonoid x →
    is-in-Large-Submonoid (raise-Large-Monoid M l2 x)
  is-closed-under-raise-subset-Large-Submonoid =
    is-closed-under-raise-subset-Large-Monoid
      ( M)
      ( subset-Large-Submonoid)

  abstract
    eq-type-Large-Submonoid :
      {l : Level} {x y : type-Large-Submonoid l} →
      inclusion-Large-Submonoid x ＝ inclusion-Large-Submonoid y →
      x ＝ y
    eq-type-Large-Submonoid =
      eq-type-Large-Subsemigroup large-subsemigroup-Large-Submonoid

open Large-Submonoid public
```

## Properties

### A large submonoid induces a large monoid

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Monoid α β}
  (S : Large-Submonoid γ M)
  where

  mul-Large-Submonoid :
    {l1 l2 : Level} →
    type-Large-Submonoid S l1 → type-Large-Submonoid S l2 →
    type-Large-Submonoid S (l1 ⊔ l2)
  mul-Large-Submonoid =
    mul-Large-Subsemigroup (large-subsemigroup-Large-Submonoid S)

  unit-Large-Submonoid : type-Large-Submonoid S lzero
  unit-Large-Submonoid =
    ( unit-Large-Monoid M ,
      contains-unit-Large-Submonoid S)

  abstract
    left-unit-law-mul-Large-Submonoid :
      {l : Level} (x : type-Large-Submonoid S l) →
      mul-Large-Submonoid unit-Large-Submonoid x ＝ x
    left-unit-law-mul-Large-Submonoid (x , _) =
      eq-type-Large-Submonoid S (left-unit-law-mul-Large-Monoid M x)

    right-unit-law-mul-Large-Submonoid :
      {l : Level} (x : type-Large-Submonoid S l) →
      mul-Large-Submonoid x unit-Large-Submonoid ＝ x
    right-unit-law-mul-Large-Submonoid (x , _) =
      eq-type-Large-Submonoid S (right-unit-law-mul-Large-Monoid M x)

  large-monoid-Large-Submonoid : Large-Monoid (λ l → α l ⊔ γ l) β
  large-monoid-Large-Submonoid =
    make-Large-Monoid
      ( large-semigroup-Large-Subsemigroup
        ( large-subsemigroup-Large-Submonoid S))
      ( unit-Large-Submonoid)
      ( left-unit-law-mul-Large-Submonoid)
      ( right-unit-law-mul-Large-Submonoid)
```

### Small submonoids from large submonoids

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Monoid α β}
  (S : Large-Submonoid γ M)
  where

  abstract
    contains-raise-unit-Large-Submonoid :
      (l : Level) → is-in-Large-Submonoid S (raise-unit-Large-Monoid M l)
    contains-raise-unit-Large-Submonoid l =
      is-closed-under-raise-subset-Large-Submonoid
        ( S)
        ( l)
        ( unit-Large-Monoid M)
        ( contains-unit-Large-Submonoid S)

  submonoid-Large-Submonoid :
    (l : Level) → Submonoid (γ l) (monoid-Large-Monoid M l)
  submonoid-Large-Submonoid l =
    ( prop-is-in-Large-Submonoid S ,
      contains-raise-unit-Large-Submonoid l ,
      is-closed-under-mul-subset-Large-Submonoid S)
```

### The inclusion homomorphism of a submonoid

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Monoid α β}
  (S : Large-Submonoid γ M)
  where

  inclusion-hom-Large-Submonoid :
    hom-Large-Monoid (large-monoid-Large-Submonoid S) M
  inclusion-hom-Large-Submonoid =
    make-hom-Large-Monoid
      ( inclusion-hom-Large-Subsemigroup (large-subsemigroup-Large-Submonoid S))
      ( refl)
```
