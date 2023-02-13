{{#title  Commutative monoids}}

```agda
module group-theory.commutative-monoids where

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

## Idea

A commutative monoid is a monoid `M` in which `xy=yx` holds for all `x,y:M`.

## Definition

```agda
is-commutative-Monoid :
  {l : Level} (M : Monoid l) → UU l
is-commutative-Monoid M =
  (x y : type-Monoid M) → Id (mul-Monoid M x y) (mul-Monoid M y x)

Commutative-Monoid : (l : Level) → UU (lsuc l)
Commutative-Monoid l = Σ (Monoid l) is-commutative-Monoid

module _
  {l : Level} (M : Commutative-Monoid l)
  where

  monoid-Commutative-Monoid : Monoid l
  monoid-Commutative-Monoid = pr1 M

  semigroup-Commutative-Monoid : Semigroup l
  semigroup-Commutative-Monoid = semigroup-Monoid monoid-Commutative-Monoid

  set-Commutative-Monoid : Set l
  set-Commutative-Monoid = set-Monoid monoid-Commutative-Monoid

  type-Commutative-Monoid : UU l
  type-Commutative-Monoid = type-Monoid monoid-Commutative-Monoid

  is-set-type-Commutative-Monoid : is-set type-Commutative-Monoid
  is-set-type-Commutative-Monoid = is-set-type-Monoid monoid-Commutative-Monoid

  mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid) → type-Commutative-Monoid
  mul-Commutative-Monoid = mul-Monoid monoid-Commutative-Monoid

  unit-Commutative-Monoid : type-Commutative-Monoid
  unit-Commutative-Monoid = unit-Monoid monoid-Commutative-Monoid
  
  associative-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    Id ( mul-Commutative-Monoid (mul-Commutative-Monoid x y) z)
       ( mul-Commutative-Monoid x (mul-Commutative-Monoid y z))
  associative-mul-Commutative-Monoid =
    associative-mul-Monoid monoid-Commutative-Monoid

  left-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid) →
    Id ( mul-Commutative-Monoid unit-Commutative-Monoid x) x
  left-unit-law-mul-Commutative-Monoid =
    left-unit-law-mul-Monoid monoid-Commutative-Monoid

  right-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid) →
    Id ( mul-Commutative-Monoid x unit-Commutative-Monoid) x
  right-unit-law-mul-Commutative-Monoid =
    right-unit-law-mul-Monoid monoid-Commutative-Monoid  
```
