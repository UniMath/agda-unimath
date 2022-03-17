# Abstract groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.abstract-groups where

open import category-theory public
open import univalent-foundations public
```

## Idea

An abstract group is a group in the usual algebraic sense, i.e., it consists of a set equipped with a unit element `e`, a binary operation `x, y ↦ xy`, and an inverse operation `x ↦ x⁻¹` satisfyint the group laws

```md
  (xy)z = x(yz)      (associativity)
     ex = x          (left unit law)
     xe = x          (right unit law)
   x⁻¹x = e          (left inverse law)
   xx⁻¹ = e          (right inverse law)
```

## Groups in Univalent Mathematics

```agda
{- The property that a monoid is a group is just the property that the monoid
   that every element is invertible, i.e., it comes equipped with an inverse
   operation that satisfies the left and right inverse laws. -}

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

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group

{- Some bureaucracy of groups -}

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
  
  associative-mul-Group : has-associative-mul type-Group
  associative-mul-Group = pr2 semigroup-Group
  
  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 associative-mul-Group

  ap-mul-Group :
    {x x' y y' : type-Group} (p : Id x x') (q : Id y y') →
    Id (mul-Group x y) (mul-Group x' y')
  ap-mul-Group p q = ap-binary mul-Group p q
  
  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x
  
  assoc-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  assoc-mul-Group = pr2 associative-mul-Group
    
  is-group-Group : is-group semigroup-Group
  is-group-Group = pr2 G
  
  is-unital-Group : is-unital semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group
  
  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group
  
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

  is-equiv-mul-Group : (x : type-Group) → is-equiv (mul-Group x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( mul-Group (inv-Group x))
      ( λ y →
        ( inv (assoc-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (right-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
      ( λ y →
        ( inv (assoc-mul-Group _ _ _)) ∙
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
        ( assoc-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (left-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
      ( λ y →
        ( assoc-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (right-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
  
  equiv-mul-Group' : (x : type-Group) → type-Group ≃ type-Group
  pr1 (equiv-mul-Group' x) = mul-Group' x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x

  equiv-conjugation-Group : (x : type-Group) → type-Group ≃ type-Group
  equiv-conjugation-Group x =
    equiv-mul-Group' (inv-Group x) ∘e equiv-mul-Group x

  transpose-eq-mul-Group :
    {x y z : type-Group} →
    Id (mul-Group x y) z → Id x (mul-Group z (inv-Group y))
  transpose-eq-mul-Group {x} {y} {z} refl =
    ( ( inv (right-unit-law-Group x)) ∙
      ( ap (mul-Group x) (inv (right-inverse-law-Group y)))) ∙
    ( inv (assoc-mul-Group x y (inv-Group y)))

  transpose-eq-mul-Group' :
    {x y z : type-Group} →
    Id (mul-Group x y) z → Id y (mul-Group (inv-Group x) z)
  transpose-eq-mul-Group' {x} {y} {z} refl =
    ( ( inv (left-unit-law-Group y)) ∙
      ( ap (mul-Group' y) (inv (left-inverse-law-Group x)))) ∙
    ( assoc-mul-Group (inv-Group x) x y)

  distributive-inv-mul-Group :
    (x y : type-Group) →
    Id (inv-Group (mul-Group x y)) (mul-Group (inv-Group y) (inv-Group x))
  distributive-inv-mul-Group x y =
    transpose-eq-mul-Group
      ( ( transpose-eq-mul-Group
          ( ( assoc-mul-Group (inv-Group (mul-Group x y)) x y) ∙
            ( left-inverse-law-Group (mul-Group x y)))) ∙
        ( left-unit-law-Group (inv-Group y)))

  conjugation-Group : (x : type-Group) → type-Group → type-Group
  conjugation-Group x = map-equiv (equiv-conjugation-Group x)

  {- We show that being a group is a proposition. -}
  
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

{- We introduce group homomorphisms. -}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group f =
    preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H) f

  type-hom-Group : UU (l1 ⊔ l2)
  type-hom-Group =
    type-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  {- Bureaucracy of group homomorphisms. -}
  
  map-hom-Group : type-hom-Group → type-Group G → type-Group H
  map-hom-Group = pr1

  preserves-mul-hom-Group :
    (f : type-hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = pr2

  emb-Group : UU (l1 ⊔ l2)
  emb-Group = Σ type-hom-Group (λ h → is-emb (map-hom-Group h))

  {- We characterize the identity type of the group homomorphisms. -}

  htpy-hom-Group : (f g : type-hom-Group) → UU (l1 ⊔ l2)
  htpy-hom-Group = htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  refl-htpy-hom-Group : (f : type-hom-Group) → htpy-hom-Group f f
  refl-htpy-hom-Group =
    refl-htpy-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  htpy-eq-hom-Group : (f g : type-hom-Group) → Id f g → htpy-hom-Group f g
  htpy-eq-hom-Group =
    htpy-eq-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  abstract
    is-contr-total-htpy-hom-Group :
      ( f : type-hom-Group) →
      is-contr (Σ type-hom-Group (htpy-hom-Group f))
    is-contr-total-htpy-hom-Group =
      is-contr-total-htpy-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : type-hom-Group) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group =
      is-equiv-htpy-eq-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  extensionality-hom-Group : (f g : type-hom-Group) → Id f g ≃ htpy-hom-Group f g
  pr1 (extensionality-hom-Group f g) = htpy-eq-hom-Group f g
  pr2 (extensionality-hom-Group f g) = is-equiv-htpy-eq-hom-Group f g

  eq-htpy-hom-Group : {f g : type-hom-Group} → htpy-hom-Group f g → Id f g
  eq-htpy-hom-Group =
    eq-htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-set-type-hom-Group : is-set type-hom-Group
  is-set-type-hom-Group =
    is-set-type-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-Group : UU-Set (l1 ⊔ l2)
  pr1 hom-Group = type-hom-Group
  pr2 hom-Group = is-set-type-hom-Group

{- We define the precategory of groups -}

id-hom-Group : {l : Level} (G : Group l) → type-hom-Group G G
id-hom-Group G = id-hom-Semigroup (semigroup-Group G)

comp-hom-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  type-hom-Group H K → type-hom-Group G H → type-hom-Group G K
comp-hom-Group G H K =
  comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)

associative-comp-hom-Group :
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  (h : type-hom-Group K L) (g : type-hom-Group H K) (f : type-hom-Group G H) →
  Id ( comp-hom-Group G H L (comp-hom-Group H K L h g) f)
     ( comp-hom-Group G K L h (comp-hom-Group G H K g f))
associative-comp-hom-Group G H K L =
  associative-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)
    ( semigroup-Group L)

left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G H H (id-hom-Group H) f) f
left-unit-law-comp-hom-Group G H =
  left-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G G H f (id-hom-Group G)) f
right-unit-law-comp-hom-Group G H =
  right-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

instance
  Group-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
  obj-Large-Precat Group-Large-Precat = Group
  hom-Large-Precat Group-Large-Precat = hom-Group
  comp-Large-Precat Group-Large-Precat {X = G} {H} {K} =
    comp-hom-Group G H K
  id-Large-Precat Group-Large-Precat {X = G} =
    id-hom-Group G
  associative-comp-Large-Precat Group-Large-Precat {X = G} {H} {K} {L} =
    associative-comp-hom-Group G H K L
  left-unit-law-comp-Large-Precat Group-Large-Precat {X = G} {H} =
    left-unit-law-comp-hom-Group G H
  right-unit-law-comp-Large-Precat Group-Large-Precat {X = G} {H} =
    right-unit-law-comp-hom-Group G H

{- We show that the precategory of groups is a category -}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where
  
  is-iso-hom-Group : type-hom-Group G H → UU (l1 ⊔ l2)
  is-iso-hom-Group = is-iso-Large-Precat Group-Large-Precat {X = G} {Y = H}

  type-iso-Group : UU (l1 ⊔ l2)
  type-iso-Group = iso-Large-Precat Group-Large-Precat G H

  hom-iso-Group : type-iso-Group → type-hom-Group G H
  hom-iso-Group = hom-iso-Large-Precat Group-Large-Precat G H

  is-iso-hom-iso-Group :
    (f : type-iso-Group) → is-iso-hom-Group (hom-iso-Group f)
  is-iso-hom-iso-Group = is-iso-hom-iso-Large-Precat Group-Large-Precat G H

  hom-inv-iso-Group : type-iso-Group → type-hom-Group H G
  hom-inv-iso-Group = hom-inv-iso-Large-Precat Group-Large-Precat G H

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group ≃ type-iso-Group
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group → type-iso-Group
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group

module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : type-iso-Group G G
  id-iso-Group = id-iso-Large-Precat Group-Large-Precat {X = G}

  iso-eq-Group : (H : Group l) → Id G H → type-iso-Group G H
  iso-eq-Group = iso-eq-Large-Precat Group-Large-Precat G

  abstract
    extensionality-Group' : (H : Group l) → Id G H ≃ type-iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)) ∘e
      ( equiv-ap-pr1 is-prop-is-group {s = G} {t = H})

  abstract
    is-contr-total-iso-Group : is-contr (Σ (Group l) (type-iso-Group G))
    is-contr-total-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-contr-total-path G)

is-category-Group : is-category-Large-Precat Group-Large-Precat
is-category-Group G =
  fundamental-theorem-id G
    ( id-iso-Group G)
    ( is-contr-total-iso-Group G)
    ( iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → type-iso-Group G H → Id G H
eq-iso-Group G H = map-inv-is-equiv (is-category-Group G H)

Group-Large-Cat : Large-Cat lsuc (λ l1 l2 → l1 ⊔ l2)
precat-Large-Cat Group-Large-Cat = Group-Large-Precat
is-category-Large-Cat Group-Large-Cat = is-category-Group
```
### Examples of groups

#### The group of integers

```agda
ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ
```

#### The group of integers modulo k

```agda
ℤ-Mod-Semigroup : (k : ℕ) → Semigroup lzero
pr1 (ℤ-Mod-Semigroup k) = ℤ-Mod-Set k
pr1 (pr2 (ℤ-Mod-Semigroup k)) = add-ℤ-Mod k
pr2 (pr2 (ℤ-Mod-Semigroup k)) = associative-add-ℤ-Mod k

ℤ-Mod-Group : (k : ℕ) → Group lzero
pr1 (ℤ-Mod-Group k) = ℤ-Mod-Semigroup k
pr1 (pr1 (pr2 (ℤ-Mod-Group k))) = zero-ℤ-Mod k
pr1 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = left-unit-law-add-ℤ-Mod k
pr2 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = right-unit-law-add-ℤ-Mod k
pr1 (pr2 (pr2 (ℤ-Mod-Group k))) = neg-ℤ-Mod k
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = left-inverse-law-add-ℤ-Mod k
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = right-inverse-law-add-ℤ-Mod k
```

#### The group of loops in a 1-type

```agda
loop-space :
  {l : Level} {A : UU l} → A → UU l
loop-space a = Id a a

loop-space-Set :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → UU-Set l
pr1 (loop-space-Set A a is-set-Ω) = Id a a
pr2 (loop-space-Set A a is-set-Ω) = is-set-Ω

loop-space-Semigroup :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Semigroup l
pr1 (loop-space-Semigroup A a is-set-Ω) = loop-space-Set A a is-set-Ω
pr1 (pr2 (loop-space-Semigroup A a is-set-Ω)) p q = p ∙ q
pr2 (pr2 (loop-space-Semigroup A a is-set-Ω)) = assoc

loop-space-Group :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Group l
pr1 (loop-space-Group A a is-set-Ω) = loop-space-Semigroup A a is-set-Ω
pr1 (pr1 (pr2 (loop-space-Group A a is-set-Ω))) = refl
pr1 (pr2 (pr1 (pr2 (loop-space-Group A a is-set-Ω)))) q = left-unit
pr2 (pr2 (pr1 (pr2 (loop-space-Group A a is-set-Ω)))) p = right-unit
pr1 (pr2 (pr2 (loop-space-Group A a is-set-Ω))) = inv
pr1 (pr2 (pr2 (pr2 (loop-space-Group A a is-set-Ω)))) = left-inv
pr2 (pr2 (pr2 (pr2 (loop-space-Group A a is-set-Ω)))) = right-inv

loop-space-1-type-Set :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → UU-Set l
loop-space-1-type-Set A a =
  loop-space-Set (type-1-Type A) a (is-1-type-type-1-Type A a a)

loop-space-1-type-Semigroup :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Semigroup l
loop-space-1-type-Semigroup A a =
  loop-space-Semigroup (type-1-Type A) a (is-1-type-type-1-Type A a a)

loop-space-1-type-Group :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Group l
loop-space-1-type-Group A a =
  loop-space-Group (type-1-Type A) a (is-1-type-type-1-Type A a a)
```

#### The symmetric group on a set

```agda
set-symmetric-Group : {l : Level} (X : UU-Set l) → UU-Set l
set-symmetric-Group X = aut-Set X

type-symmetric-Group : {l : Level} (X : UU-Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : UU-Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-mul-Set (aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → is-unital (symmetric-Semigroup X)
pr1 (is-unital-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : UU-Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → UU-Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise

{- We show that group homomorphisms preserve the unit. -}

preserves-unit :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : type-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)) →
  UU l2
preserves-unit G H f =
  Id (map-hom-Group G H f (unit-Group G)) (unit-Group H)

abstract
  preserves-unit-hom-Group :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) → preserves-unit G H f
  preserves-unit-hom-Group G H f =
    ( inv (left-unit-law-Group H (map-hom-Group G H f (unit-Group G)))) ∙
    ( ( ap ( λ x → mul-Group H x (map-hom-Group G H f (unit-Group G)))
           ( inv
             ( left-inverse-law-Group H
               ( map-hom-Group G H f (unit-Group G))))) ∙
      ( ( assoc-mul-Group H
          ( inv-Group H (map-hom-Group G H f (unit-Group G)))
          ( map-hom-Group G H f (unit-Group G))
          ( map-hom-Group G H f (unit-Group G))) ∙
        ( ( ap
            ( mul-Group H (inv-Group H (map-hom-Group G H f (unit-Group G))))
            ( inv
              ( preserves-mul-hom-Group G H f (unit-Group G) (unit-Group G)))) ∙
          ( ( ap
              ( λ x →
                mul-Group H
                  ( inv-Group H (map-hom-Group G H f (unit-Group G)))
                  ( map-hom-Group G H f x))
              ( left-unit-law-Group G (unit-Group G))) ∙
            ( left-inverse-law-Group H (map-hom-Group G H f (unit-Group G)))))))

{- We show that group homomorphisms preserve inverses. -}

preserves-inverses :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : type-hom-Group G H) → UU (l1 ⊔ l2)
preserves-inverses G H f =
  ( x : type-Group G) →
  Id ( map-hom-Group G H f (inv-Group G x))
     ( inv-Group H (map-hom-Group G H f x))

abstract
  preserves-inverses-hom-Group' :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) →
    preserves-unit G H f → preserves-inverses G H f
  preserves-inverses-hom-Group'
    ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
           ( pair ( pair e-G (pair left-unit-G right-unit-G))
                  ( pair i-G (pair left-inv-G right-inv-G))))
    ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
           ( pair ( pair e-H (pair left-unit-H right-unit-H))
                  ( pair i-H (pair left-inv-H right-inv-H))))
    ( pair f μ-f) preserves-unit-f x =
    ( inv ( right-unit-H (f (i-G x)))) ∙
    ( ( ap (μ-H (f (i-G x))) (inv (right-inv-H (f x)))) ∙
      ( ( inv (assoc-H (f (i-G x)) (f x) (i-H (f x)))) ∙
        ( ( inv (ap (λ y → μ-H y (i-H (f x))) (μ-f (i-G x) x))) ∙
          ( ( ap (λ y → μ-H (f y) (i-H (f x))) (left-inv-G x)) ∙
            ( ( ap
                ( λ y → μ-H y (i-H (f x)))
                ( preserves-unit-f)) ∙
              ( left-unit-H (i-H (f x))))))))

abstract
  preserves-inverses-hom-Group :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) → preserves-inverses G H f
  preserves-inverses-hom-Group G H f =
    preserves-inverses-hom-Group' G H f (preserves-unit-hom-Group G H f)

hom-Group' :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group' G H =
  Σ ( type-hom-Group G H) (λ f →
    ( preserves-unit G H f) × (preserves-inverses G H f))

preserves-group-structure-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  type-hom-Group G H → hom-Group' G H
pr1 (preserves-group-structure-hom-Group G H f) = f
pr1 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-unit-hom-Group G H f
pr2 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-inverses-hom-Group G H f

--------------------------------------------------------------------------------

-- Cayley's Theorem

module _
  {l1 : Level} (G : Group l1)
  where
  
  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem x = equiv-mul-Group G x
  
  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem x y =
    eq-htpy-equiv (λ z → assoc-mul-Group G x y z)

  hom-Cayleys-theorem : type-hom-Group G (symmetric-Group (set-Group G))
  hom-Cayleys-theorem =
    pair map-Cayleys-theorem preserves-mul-map-Cayleys-theorem

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p =
    ( inv (right-unit-law-Group G x)) ∙
    ( ( htpy-eq-equiv p (unit-Group G)) ∙
      ( right-unit-law-Group G y))

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem =
    is-emb-is-injective
      ( is-set-type-Group (symmetric-Group (set-Group G)))
      ( is-injective-map-Cayleys-theorem)

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  Cayleys-theorem = pair hom-Cayleys-theorem is-emb-map-Cayleys-theorem
```
