# Abstract groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.groups where

open import foundation.binary-embeddings using
  ( is-binary-emb; is-binary-emb-is-binary-equiv)
open import foundation.binary-equivalences using (is-binary-equiv)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; is-emb-is-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.identity-types using (Id; ap-binary; inv; _∙_; ap; refl)
open import foundation.injective-maps using
  ( is-injective; is-injective-is-equiv)
open import foundation.propositions using
  ( all-elements-equal; is-prop-all-elements-equal; is-prop; prod-Prop; Π-Prop;
    is-prop-Σ; UU-Prop)
open import foundation.sets using (UU-Set; is-set; type-Set; Id-Prop)
open import foundation.subtypes using (eq-subtype)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.monoids using
  ( is-unital; Monoid; is-prop-is-unital)
open import group-theory.semigroups using
  ( Semigroup; type-Semigroup; mul-Semigroup; has-associative-mul)

open import univalent-combinatorics.lists using
  ( list; mul-list-Monoid; distributive-mul-list-Monoid; concat-list)
```

## Idea

An abstract group is a group in the usual algebraic sense, i.e., it consists of a set equipped with a unit element `e`, a binary operation `x, y ↦ xy`, and an inverse operation `x ↦ x⁻¹` satisfying the group laws

```md
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Groups in Univalent Mathematics

### The condition that a semigroup is a group

```agda
is-group' :
  {l : Level} (G : Semigroup l) → is-unital G → UU l
is-group' G is-unital-G =
  Σ ( type-Semigroup G → type-Semigroup G)
    ( λ i →
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G (i x) x) (pr1 is-unital-G)) ×
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G x (i x)) (pr1 is-unital-G)))

is-group :
  {l : Level} (G : Semigroup l) → UU l
is-group G =
  Σ (is-unital G) (is-group' G)
```

### The type of groups

```agda
Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group

module _
  {l : Level} (G : Group l)
  where
  
  semigroup-Group : Semigroup l
  semigroup-Group = pr1 G
  
  set-Group : UU-Set l
  set-Group = pr1 semigroup-Group
  
  type-Group : UU l
  type-Group = pr1 set-Group
  
  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group
  
  has-associative-mul-Group : has-associative-mul type-Group
  has-associative-mul-Group = pr2 semigroup-Group
  
  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 has-associative-mul-Group

  ap-mul-Group :
    {x x' y y' : type-Group} (p : Id x x') (q : Id y y') →
    Id (mul-Group x y) (mul-Group x' y')
  ap-mul-Group p q = ap-binary mul-Group p q
  
  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x
  
  associative-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  associative-mul-Group = pr2 has-associative-mul-Group
    
  is-group-Group : is-group semigroup-Group
  is-group-Group = pr2 G
  
  is-unital-Group : is-unital semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group
  
  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group

  is-unit-Group : type-Group → UU l
  is-unit-Group x = Id x unit-Group
  
  left-unit-law-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-Group = pr1 (pr2 is-unital-Group)
  
  right-unit-law-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-Group = pr2 (pr2 is-unital-Group)
  
  has-inverses-Group : is-group' semigroup-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group
  
  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group
  
  left-inverse-law-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-Group = pr1 (pr2 has-inverses-Group)
  
  right-inverse-law-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-Group = pr2 (pr2 has-inverses-Group)

  is-own-inverse-unit-Group :
    Id (inv-Group unit-Group) unit-Group
  is-own-inverse-unit-Group =
    ( inv (left-unit-law-Group (inv-Group unit-Group))) ∙
      ( right-inverse-law-Group unit-Group)

  is-equiv-mul-Group : (x : type-Group) → is-equiv (mul-Group x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( mul-Group (inv-Group x))
      ( λ y →
        ( inv (associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (right-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
      ( λ y →
        ( inv (associative-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (left-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
  
  equiv-mul-Group : (x : type-Group) → type-Group ≃ type-Group
  pr1 (equiv-mul-Group x) = mul-Group x
  pr2 (equiv-mul-Group x) = is-equiv-mul-Group x
  
  is-equiv-mul-Group' : (x : type-Group) → is-equiv (mul-Group' x)
  is-equiv-mul-Group' x =
    is-equiv-has-inverse
    ( mul-Group' (inv-Group x))
      ( λ y →
        ( associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (left-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
      ( λ y →
        ( associative-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (right-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
  
  equiv-mul-Group' : (x : type-Group) → type-Group ≃ type-Group
  pr1 (equiv-mul-Group' x) = mul-Group' x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x

  is-binary-equiv-mul-Group : is-binary-equiv mul-Group
  pr1 is-binary-equiv-mul-Group = is-equiv-mul-Group'
  pr2 is-binary-equiv-mul-Group = is-equiv-mul-Group

  is-binary-emb-mul-Group : is-binary-emb mul-Group
  is-binary-emb-mul-Group =
    is-binary-emb-is-binary-equiv is-binary-equiv-mul-Group

  is-emb-mul-Group : (x : type-Group) → is-emb (mul-Group x)
  is-emb-mul-Group x = is-emb-is-equiv (is-equiv-mul-Group x)

  is-emb-mul-Group' : (x : type-Group) → is-emb (mul-Group' x)
  is-emb-mul-Group' x = is-emb-is-equiv (is-equiv-mul-Group' x)

  is-injective-mul-Group : (x : type-Group) → is-injective (mul-Group x)
  is-injective-mul-Group x = is-injective-is-equiv (is-equiv-mul-Group x)

  is-injective-mul-Group' : (x : type-Group) → is-injective (mul-Group' x)
  is-injective-mul-Group' x = is-injective-is-equiv (is-equiv-mul-Group' x)

  transpose-eq-mul-Group :
    {x y z : type-Group} →
    Id (mul-Group x y) z → Id x (mul-Group z (inv-Group y))
  transpose-eq-mul-Group {x} {y} {z} refl =
    ( ( inv (right-unit-law-Group x)) ∙
      ( ap (mul-Group x) (inv (right-inverse-law-Group y)))) ∙
    ( inv (associative-mul-Group x y (inv-Group y)))

  transpose-eq-mul-Group' :
    {x y z : type-Group} →
    Id (mul-Group x y) z → Id y (mul-Group (inv-Group x) z)
  transpose-eq-mul-Group' {x} {y} {z} refl =
    ( ( inv (left-unit-law-Group y)) ∙
      ( ap (mul-Group' y) (inv (left-inverse-law-Group x)))) ∙
    ( associative-mul-Group (inv-Group x) x y)

  distributive-inv-mul-Group :
    (x y : type-Group) →
    Id (inv-Group (mul-Group x y)) (mul-Group (inv-Group y) (inv-Group x))
  distributive-inv-mul-Group x y =
    transpose-eq-mul-Group
      ( ( transpose-eq-mul-Group
          ( ( associative-mul-Group (inv-Group (mul-Group x y)) x y) ∙
            ( left-inverse-law-Group (mul-Group x y)))) ∙
        ( left-unit-law-Group (inv-Group y)))
        
  inv-inv-Group :
    (x : type-Group) → Id (inv-Group (inv-Group x)) x
  inv-inv-Group x =
    is-injective-mul-Group
      ( inv-Group x)
      ( ( right-inverse-law-Group (inv-Group x)) ∙
        ( inv (left-inverse-law-Group x)))
```

## Properties

### For any semigroup, being a group is a property

```agda
abstract
  all-elements-equal-is-group :
    {l : Level} (G : Semigroup l) (e : is-unital G) →
    all-elements-equal (is-group' G e)
  all-elements-equal-is-group
    ( pair G (pair μ assoc-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-subtype
      ( λ i →
        prod-Prop
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ (i x) x) e))
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →                                             -- ix
          ( inv (left-unit-G (i x))) ∙                      -- = 1·(ix)
          ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
            ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·ix)
              ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
                ( right-unit-G (i' x)))))))                 -- = i'x

abstract
  is-prop-is-group :
    {l : Level} (G : Semigroup l) → is-prop (is-group G)
  is-prop-is-group G =
    is-prop-Σ
      ( is-prop-is-unital G)
      ( λ e →
        is-prop-all-elements-equal (all-elements-equal-is-group G e))

is-group-Prop : {l : Level} (G : Semigroup l) → UU-Prop l
pr1 (is-group-Prop G) = is-group G
pr2 (is-group-Prop G) = is-prop-is-group G
```

### Any idempotent element in a group is the unit

```agda
module _
  {l : Level} (G : Group l)
  where
  
  is-idempotent-Group : type-Group G → UU l
  is-idempotent-Group x = Id (mul-Group G x x) x

  is-unit-is-idempotent-Group :
    {x : type-Group G} → is-idempotent-Group x → is-unit-Group G x
  is-unit-is-idempotent-Group {x} p =
    is-injective-mul-Group G x (p ∙ inv (right-unit-law-Group G x))
```

### Multiplication of a list of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where
  
  mul-list-Group : list (type-Group G) → type-Group G
  mul-list-Group = mul-list-Monoid (monoid-Group G)

  preserves-concat-mul-list-Group :
    (l1 l2 : list (type-Group G)) →
    Id ( mul-list-Group (concat-list l1 l2))
       ( mul-Group G (mul-list-Group l1) (mul-list-Group l2))
  preserves-concat-mul-list-Group =
    distributive-mul-list-Monoid (monoid-Group G)
```
