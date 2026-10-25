# Large commutative submonoids

```agda
module group-theory.large-commutative-submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-large-commutative-monoids
open import group-theory.large-commutative-monoids
open import group-theory.large-monoids
open import group-theory.large-submonoids
open import group-theory.submonoids-commutative-monoids
```

</details>

## Idea

A
{{#concept "submonoid" Disambiguation="of a large commutative monoid" Agda=Large-Commutative-Submonoid}}
of a [large commutative monoid](group-theory.large-commutative-monoids.md) `M`
is a [subset](group-theory.subsets-large-commutative-monoids.md) of `M` that is
closed under multiplication and contains the unit.

## Definition

We create a one-field record instead of an alias to ensure that, consistent with
other large algebraic structures, the ambient large commutative monoid can be
inferred from the large commutative submonoid.

```agda
record
  Large-Commutative-Submonoid
    {α : Level → Level}
    {β : Level → Level → Level}
    (γ : Level → Level)
    (M : Large-Commutative-Monoid α β) :
    UUω
  where

  constructor
    make-Large-Commutative-Submonoid

  field
    large-submonoid-Large-Commutative-Submonoid :
      Large-Submonoid γ (large-monoid-Large-Commutative-Monoid M)

  type-Large-Commutative-Submonoid : (l : Level) → UU (α l ⊔ γ l)
  type-Large-Commutative-Submonoid =
    type-Large-Submonoid large-submonoid-Large-Commutative-Submonoid

  inclusion-Large-Commutative-Submonoid :
    {l : Level} →
    type-Large-Commutative-Submonoid l → type-Large-Commutative-Monoid M l
  inclusion-Large-Commutative-Submonoid = pr1

  abstract
    eq-type-Large-Commutative-Submonoid :
      {l : Level} {x y : type-Large-Commutative-Submonoid l} →
      ( inclusion-Large-Commutative-Submonoid x ＝
        inclusion-Large-Commutative-Submonoid y) →
      x ＝ y
    eq-type-Large-Commutative-Submonoid =
      eq-type-Large-Submonoid large-submonoid-Large-Commutative-Submonoid

open Large-Commutative-Submonoid public
```

## Properties

### A large commutative submonoid induces a large commutative monoid

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Commutative-Monoid α β}
  (S : Large-Commutative-Submonoid γ M)
  where

  large-monoid-Large-Commutative-Submonoid :
    Large-Monoid (λ l → α l ⊔ γ l) β
  large-monoid-Large-Commutative-Submonoid =
    large-monoid-Large-Submonoid
      ( large-submonoid-Large-Commutative-Submonoid S)

  mul-Large-Commutative-Submonoid :
    {l1 l2 : Level} →
    type-Large-Commutative-Submonoid S l1 →
    type-Large-Commutative-Submonoid S l2 →
    type-Large-Commutative-Submonoid S (l1 ⊔ l2)
  mul-Large-Commutative-Submonoid =
    mul-Large-Monoid large-monoid-Large-Commutative-Submonoid

  abstract
    commutative-mul-Large-Commutative-Submonoid :
      {l1 l2 : Level}
      (x : type-Large-Commutative-Submonoid S l1)
      (y : type-Large-Commutative-Submonoid S l2) →
      mul-Large-Commutative-Submonoid x y ＝
      mul-Large-Commutative-Submonoid y x
    commutative-mul-Large-Commutative-Submonoid (x , _) (y , _) =
      eq-type-Large-Commutative-Submonoid
        ( S)
        ( commutative-mul-Large-Commutative-Monoid M x y)

  large-commutative-monoid-Large-Commutative-Submonoid :
    Large-Commutative-Monoid (λ l → α l ⊔ γ l) β
  large-commutative-monoid-Large-Commutative-Submonoid =
    make-Large-Commutative-Monoid
      ( large-monoid-Large-Commutative-Submonoid)
      ( commutative-mul-Large-Commutative-Submonoid)
```

### The inclusion homomorphism of a large commutative submonoid

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Commutative-Monoid α β}
  (S : Large-Commutative-Submonoid γ M)
  where

  inclusion-hom-Large-Commutative-Submonoid :
    hom-Large-Commutative-Monoid
      ( large-commutative-monoid-Large-Commutative-Submonoid S)
      ( M)
  inclusion-hom-Large-Commutative-Submonoid =
    make-hom-Large-Commutative-Monoid
      ( inclusion-hom-Large-Submonoid
        ( large-submonoid-Large-Commutative-Submonoid S))
```

### Small commutative submonoids from large commutative submonoids

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {M : Large-Commutative-Monoid α β}
  (S : Large-Commutative-Submonoid γ M)
  where

  commutative-submonoid-Large-Commutative-Submonoid :
    (l : Level) →
    Commutative-Submonoid
      ( γ l)
      ( commutative-monoid-Large-Commutative-Monoid M l)
  commutative-submonoid-Large-Commutative-Submonoid =
    submonoid-Large-Submonoid (large-submonoid-Large-Commutative-Submonoid S)
```
