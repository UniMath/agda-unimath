# Abelian groups

```agda
module group-theory.abelian-groups where
```

<details><summary>Imports</summary>
```agda
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
open import univalent-combinatorics.lists
```
</details>

## Idea

Abelian groups are groups of which the group operation is commutative

## Definition

```agda
is-abelian-group-Prop : {l : Level} → Group l → Prop l
is-abelian-group-Prop G =
  Π-Prop
    ( type-Group G)
    ( λ x →
      Π-Prop
        ( type-Group G)
        ( λ y → Id-Prop (set-Group G) (mul-Group G x y) (mul-Group G y x)))

is-abelian-Group : {l : Level} → Group l → UU l
is-abelian-Group G = type-Prop (is-abelian-group-Prop G)

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G = is-prop-type-Prop (is-abelian-group-Prop G)

Ab : (l : Level) → UU (lsuc l)
Ab l = Σ (Group l) is-abelian-Group
```

```agda
module _
  {l : Level} (A : Ab l)
  where

  group-Ab : Group l
  group-Ab = pr1 A

  set-Ab : Set l
  set-Ab = set-Group group-Ab

  type-Ab : UU l
  type-Ab = type-Group group-Ab

  is-set-type-Ab : is-set type-Ab
  is-set-type-Ab = is-set-type-Group group-Ab

  has-associative-add-Ab : has-associative-mul-Set set-Ab
  has-associative-add-Ab = has-associative-mul-Group group-Ab

  add-Ab : type-Ab → type-Ab → type-Ab
  add-Ab = mul-Group group-Ab

  add-Ab' : type-Ab → type-Ab → type-Ab
  add-Ab' = mul-Group' group-Ab

  ap-add-Ab :
    {x y x' y' : type-Ab} → x ＝ x' → y ＝ y' → add-Ab x y ＝ add-Ab x' y'
  ap-add-Ab p q = ap-binary add-Ab p q

  associative-add-Ab :
    (x y z : type-Ab ) → add-Ab (add-Ab x y) z ＝ add-Ab x (add-Ab y z)
  associative-add-Ab = associative-mul-Group group-Ab

  semigroup-Ab : Semigroup l
  semigroup-Ab = semigroup-Group group-Ab

  is-group-Ab : is-group semigroup-Ab
  is-group-Ab = is-group-Group group-Ab

  has-zero-Ab : is-unital-Semigroup semigroup-Ab
  has-zero-Ab = is-unital-Group group-Ab

  zero-Ab : type-Ab
  zero-Ab = unit-Group group-Ab

  is-zero-Ab : type-Ab → UU l
  is-zero-Ab x = x ＝ zero-Ab

  left-unit-law-add-Ab : (x : type-Ab) → add-Ab zero-Ab x ＝ x
  left-unit-law-add-Ab = left-unit-law-mul-Group group-Ab

  right-unit-law-add-Ab : (x : type-Ab) → add-Ab x zero-Ab ＝ x
  right-unit-law-add-Ab = right-unit-law-mul-Group group-Ab

  has-negatives-Ab : is-group' semigroup-Ab has-zero-Ab
  has-negatives-Ab = has-inverses-Group group-Ab

  neg-Ab : type-Ab → type-Ab
  neg-Ab = inv-Group group-Ab

  left-inverse-law-add-Ab : (x : type-Ab) → add-Ab (neg-Ab x) x ＝ zero-Ab
  left-inverse-law-add-Ab = left-inverse-law-mul-Group group-Ab

  right-inverse-law-add-Ab : (x : type-Ab) → add-Ab x (neg-Ab x) ＝ zero-Ab
  right-inverse-law-add-Ab = right-inverse-law-mul-Group group-Ab

  commutative-add-Ab : (x y : type-Ab) → Id (add-Ab x y) (add-Ab y x)
  commutative-add-Ab = pr2 A

  interchange-add-add-Ab :
    (a b c d : type-Ab) →
    add-Ab (add-Ab a b) (add-Ab c d) ＝ add-Ab (add-Ab a c) (add-Ab b d)
  interchange-add-add-Ab =
    interchange-law-commutative-and-associative
      add-Ab
      commutative-add-Ab
      associative-add-Ab

  right-swap-add-Ab :
    (a b c : type-Ab) → add-Ab (add-Ab a b) c ＝ add-Ab (add-Ab a c) b
  right-swap-add-Ab a b c =
    ( associative-add-Ab a b c) ∙
    ( ( ap (add-Ab a) (commutative-add-Ab b c)) ∙
      ( inv (associative-add-Ab a c b)))

  left-swap-add-Ab :
    (a b c : type-Ab) → add-Ab a (add-Ab b c) ＝ add-Ab b (add-Ab a c)
  left-swap-add-Ab a b c =
    ( inv (associative-add-Ab a b c)) ∙
    ( ( ap (add-Ab' c) (commutative-add-Ab a b)) ∙
      ( associative-add-Ab b a c))

  distributive-neg-add-Ab :
    (x y : type-Ab) →
    neg-Ab (add-Ab x y) ＝ add-Ab (neg-Ab x) (neg-Ab y)
  distributive-neg-add-Ab x y =
    ( distributive-inv-mul-Group group-Ab x y) ∙
    ( commutative-add-Ab (neg-Ab y) (neg-Ab x))

  neg-neg-Ab : (x : type-Ab) → neg-Ab (neg-Ab x) ＝ x
  neg-neg-Ab = inv-inv-Group group-Ab

  neg-zero-Ab : neg-Ab zero-Ab ＝ zero-Ab
  neg-zero-Ab = inv-unit-Group group-Ab
```

## Properties

### Abelian groups are commutative monoids

```agda
module _
  {l : Level} (A : Ab l)
  where

  monoid-Ab : Monoid l
  pr1 monoid-Ab = semigroup-Ab A
  pr1 (pr2 monoid-Ab) = zero-Ab A
  pr1 (pr2 (pr2 monoid-Ab)) = left-unit-law-add-Ab A
  pr2 (pr2 (pr2 monoid-Ab)) = right-unit-law-add-Ab A

  commutative-monoid-Ab : Commutative-Monoid l
  pr1 commutative-monoid-Ab = monoid-Ab
  pr2 commutative-monoid-Ab = commutative-add-Ab A
```

### Addition on an abelian group is a binary equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-equiv-add-Ab : (x : type-Ab A) → is-equiv (add-Ab A x)
  is-equiv-add-Ab = is-equiv-mul-Group (group-Ab A)

  is-equiv-add-Ab' : (x : type-Ab A) → is-equiv (add-Ab' A x)
  is-equiv-add-Ab' = is-equiv-mul-Group' (group-Ab A)

  is-binary-equiv-add-Ab : is-binary-equiv (add-Ab A)
  is-binary-equiv-add-Ab = is-binary-equiv-mul-Group (group-Ab A)
```

### Addition on an abelian group is a binary embedding

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-emb-add-Ab : is-binary-emb (add-Ab A)
  is-binary-emb-add-Ab = is-binary-emb-mul-Group (group-Ab A)

  is-emb-add-Ab : (x : type-Ab A) → is-emb (add-Ab A x)
  is-emb-add-Ab = is-emb-mul-Group (group-Ab A)

  is-emb-add-Ab' : (x : type-Ab A) → is-emb (add-Ab' A x)
  is-emb-add-Ab' = is-emb-mul-Group' (group-Ab A)
```

### Addition on an abelian group is pointwise injective from both sides

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-injective-add-Ab : (x : type-Ab A) → is-injective (add-Ab A x)
  is-injective-add-Ab = is-injective-mul-Group (group-Ab A)

  is-injective-add-Ab' : (x : type-Ab A) → is-injective (add-Ab' A x)
  is-injective-add-Ab' = is-injective-mul-Group' (group-Ab A)
```

### Transposing identifications in abelian groups

```agda
module _
  {l : Level} (A : Ab l)
  where

  transpose-eq-add-Ab :
    {x y z : type-Ab A} → Id (add-Ab A x y) z → Id x (add-Ab A z (neg-Ab A y))
  transpose-eq-add-Ab = transpose-eq-mul-Group (group-Ab A)

  transpose-eq-add-Ab' :
    {x y z : type-Ab A} → Id (add-Ab A x y) z → Id y (add-Ab A (neg-Ab A x) z)
  transpose-eq-add-Ab' = transpose-eq-mul-Group' (group-Ab A)
```

### Any idempotent element in an abelian group is zero

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-idempotent-Ab : type-Ab A → UU l
  is-idempotent-Ab = is-idempotent-Group (group-Ab A)

  is-zero-is-idempotent-Ab :
    {x : type-Ab A} → is-idempotent-Ab x → is-zero-Ab A x
  is-zero-is-idempotent-Ab = is-unit-is-idempotent-Group (group-Ab A)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-list-Ab : list (type-Ab A) → type-Ab A
  add-list-Ab = mul-list-Group (group-Ab A)

  preserves-concat-add-list-Ab :
    (l1 l2 : list (type-Ab A)) →
    Id ( add-list-Ab (concat-list l1 l2))
       ( add-Ab A (add-list-Ab l1) (add-list-Ab l2))
  preserves-concat-add-list-Ab = preserves-concat-mul-list-Group (group-Ab A)
```
