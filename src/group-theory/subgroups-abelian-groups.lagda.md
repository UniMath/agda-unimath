# Subgroups of abelian groups

```agda
module group-theory.subgroups-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.normal-subgroups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subsets-abelian-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definitions

### Subgroups of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A)
  where

  contains-zero-subset-Ab : UU l2
  contains-zero-subset-Ab = contains-unit-subset-Group (group-Ab A) P

  is-prop-contains-zero-subset-Ab : is-prop contains-zero-subset-Ab
  is-prop-contains-zero-subset-Ab =
    is-prop-contains-unit-subset-Group (group-Ab A) P

  is-closed-under-addition-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ab =
    is-closed-under-multiplication-subset-Group (group-Ab A) P

  is-prop-is-closed-under-addition-subset-Ab :
    is-prop is-closed-under-addition-subset-Ab
  is-prop-is-closed-under-addition-subset-Ab =
    is-prop-is-closed-under-multiplication-subset-Group (group-Ab A) P

  is-closed-under-negatives-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ab =
    is-closed-under-inverses-subset-Group (group-Ab A) P

  is-prop-closed-under-neg-subset-Ab :
    is-prop is-closed-under-negatives-subset-Ab
  is-prop-closed-under-neg-subset-Ab =
    is-prop-is-closed-under-inverses-subset-Group (group-Ab A) P

  is-subgroup-Ab : UU (l1 ⊔ l2)
  is-subgroup-Ab = is-subgroup-subset-Group (group-Ab A) P

  is-prop-is-subgroup-Ab : is-prop is-subgroup-Ab
  is-prop-is-subgroup-Ab = is-prop-is-subgroup-subset-Group (group-Ab A) P
```

### The type of all subgroups of an abelian group

```agda
Subgroup-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU (lsuc l ⊔ l1)
Subgroup-Ab l A = Subgroup l (group-Ab A)

module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  subset-Subgroup-Ab : subset-Ab l2 A
  subset-Subgroup-Ab = subset-Subgroup (group-Ab A) B

  type-Subgroup-Ab : UU (l1 ⊔ l2)
  type-Subgroup-Ab = type-Subgroup (group-Ab A) B

  inclusion-Subgroup-Ab : type-Subgroup-Ab → type-Ab A
  inclusion-Subgroup-Ab = inclusion-Subgroup (group-Ab A) B

  is-emb-inclusion-Subgroup-Ab : is-emb inclusion-Subgroup-Ab
  is-emb-inclusion-Subgroup-Ab =
    is-emb-inclusion-Subgroup (group-Ab A) B

  emb-inclusion-Subgroup-Ab : type-Subgroup-Ab ↪ type-Ab A
  emb-inclusion-Subgroup-Ab = emb-inclusion-Subgroup (group-Ab A) B

  is-in-Subgroup-Ab : type-Ab A → UU l2
  is-in-Subgroup-Ab = is-in-Subgroup (group-Ab A) B

  is-closed-under-eq-Subgroup-Ab :
    {x y : type-Ab A} →
    is-in-Subgroup-Ab x → x ＝ y → is-in-Subgroup-Ab y
  is-closed-under-eq-Subgroup-Ab =
    is-closed-under-eq-Subgroup (group-Ab A) B

  is-closed-under-eq-Subgroup-Ab' :
    {x y : type-Ab A} →
    is-in-Subgroup-Ab y → x ＝ y → is-in-Subgroup-Ab x
  is-closed-under-eq-Subgroup-Ab' =
    is-closed-under-eq-Subgroup' (group-Ab A) B

  is-in-subgroup-inclusion-Subgroup-Ab :
    (x : type-Subgroup-Ab) →
    is-in-Subgroup-Ab (inclusion-Subgroup-Ab x)
  is-in-subgroup-inclusion-Subgroup-Ab =
    is-in-subgroup-inclusion-Subgroup (group-Ab A) B

  is-prop-is-in-Subgroup-Ab :
    (x : type-Ab A) → is-prop (is-in-Subgroup-Ab x)
  is-prop-is-in-Subgroup-Ab =
    is-prop-is-in-Subgroup (group-Ab A) B

  is-subgroup-Subgroup-Ab :
    is-subgroup-Ab A subset-Subgroup-Ab
  is-subgroup-Subgroup-Ab = is-subgroup-Subgroup (group-Ab A) B

  contains-zero-Subgroup-Ab :
    contains-zero-subset-Ab A subset-Subgroup-Ab
  contains-zero-Subgroup-Ab = contains-unit-Subgroup (group-Ab A) B

  is-closed-under-addition-Subgroup-Ab :
    is-closed-under-addition-subset-Ab A subset-Subgroup-Ab
  is-closed-under-addition-Subgroup-Ab =
    is-closed-under-multiplication-Subgroup (group-Ab A) B

  is-closed-under-negatives-Subgroup-Ab :
    is-closed-under-negatives-subset-Ab A subset-Subgroup-Ab
  is-closed-under-negatives-Subgroup-Ab =
    is-closed-under-inverses-Subgroup (group-Ab A) B

  is-in-subgroup-left-summand-Subgroup-Ab :
    (x y : type-Ab A) →
    is-in-Subgroup-Ab (add-Ab A x y) → is-in-Subgroup-Ab y →
    is-in-Subgroup-Ab x
  is-in-subgroup-left-summand-Subgroup-Ab =
    is-in-subgroup-left-factor-Subgroup (group-Ab A) B

  is-in-subgroup-right-summand-Subgroup-Ab :
    (x y : type-Ab A) →
    is-in-Subgroup-Ab (add-Ab A x y) → is-in-Subgroup-Ab x →
    is-in-Subgroup-Ab y
  is-in-subgroup-right-summand-Subgroup-Ab =
    is-in-subgroup-right-factor-Subgroup (group-Ab A) B

is-emb-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → is-emb (subset-Subgroup-Ab {l2 = l2} A)
is-emb-subset-Subgroup-Ab A = is-emb-subset-Subgroup (group-Ab A)
```

### The underlying abelian group of a subgroup of an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  type-ab-Subgroup-Ab : UU (l1 ⊔ l2)
  type-ab-Subgroup-Ab = type-group-Subgroup (group-Ab A) B

  map-inclusion-Subgroup-Ab : type-ab-Subgroup-Ab → type-Ab A
  map-inclusion-Subgroup-Ab = map-inclusion-Subgroup (group-Ab A) B

  is-emb-incl-ab-Subgroup-Ab : is-emb map-inclusion-Subgroup-Ab
  is-emb-incl-ab-Subgroup-Ab = is-emb-inclusion-Subgroup (group-Ab A) B

  eq-subgroup-ab-eq-ab :
    {x y : type-ab-Subgroup-Ab} →
    map-inclusion-Subgroup-Ab x ＝ map-inclusion-Subgroup-Ab y →
    x ＝ y
  eq-subgroup-ab-eq-ab = eq-subgroup-eq-group (group-Ab A) B

  set-ab-Subgroup-Ab : Set (l1 ⊔ l2)
  set-ab-Subgroup-Ab = set-group-Subgroup (group-Ab A) B

  zero-ab-Subgroup-Ab : type-ab-Subgroup-Ab
  zero-ab-Subgroup-Ab = unit-Subgroup (group-Ab A) B

  add-ab-Subgroup-Ab : (x y : type-ab-Subgroup-Ab) → type-ab-Subgroup-Ab
  add-ab-Subgroup-Ab = mul-Subgroup (group-Ab A) B

  neg-ab-Subgroup-Ab : type-ab-Subgroup-Ab → type-ab-Subgroup-Ab
  neg-ab-Subgroup-Ab = inv-Subgroup (group-Ab A) B

  associative-add-Subgroup-Ab :
    ( x y z : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab (add-ab-Subgroup-Ab x y) z ＝
    add-ab-Subgroup-Ab x (add-ab-Subgroup-Ab y z)
  associative-add-Subgroup-Ab =
    associative-mul-Subgroup (group-Ab A) B

  left-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab zero-ab-Subgroup-Ab x ＝ x
  left-unit-law-add-Subgroup-Ab =
    left-unit-law-mul-Subgroup (group-Ab A) B

  right-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab x zero-ab-Subgroup-Ab ＝ x
  right-unit-law-add-Subgroup-Ab =
    right-unit-law-mul-Subgroup (group-Ab A) B

  left-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab (neg-ab-Subgroup-Ab x) x ＝ zero-ab-Subgroup-Ab
  left-inverse-law-add-Subgroup-Ab =
    left-inverse-law-mul-Subgroup (group-Ab A) B

  right-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab x (neg-ab-Subgroup-Ab x) ＝ zero-ab-Subgroup-Ab
  right-inverse-law-add-Subgroup-Ab =
    right-inverse-law-mul-Subgroup (group-Ab A) B

  commutative-add-Subgroup-Ab :
    ( x y : type-ab-Subgroup-Ab) →
    add-ab-Subgroup-Ab x y ＝ add-ab-Subgroup-Ab y x
  commutative-add-Subgroup-Ab x y =
    eq-subgroup-ab-eq-ab (commutative-add-Ab A (pr1 x) (pr1 y))

  semigroup-Subgroup-Ab : Semigroup (l1 ⊔ l2)
  semigroup-Subgroup-Ab = semigroup-Subgroup (group-Ab A) B

  group-Subgroup-Ab : Group (l1 ⊔ l2)
  group-Subgroup-Ab = group-Subgroup (group-Ab A) B

  ab-Subgroup-Ab : Ab (l1 ⊔ l2)
  pr1 ab-Subgroup-Ab = group-Subgroup-Ab
  pr2 ab-Subgroup-Ab = commutative-add-Subgroup-Ab
```

### The inclusion of the underlying group of a subgroup into the ambient abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  preserves-add-inclusion-Subgroup-Ab :
    preserves-add-Ab (ab-Subgroup-Ab A B) A (map-inclusion-Subgroup-Ab A B)
  preserves-add-inclusion-Subgroup-Ab {x} {y} =
    preserves-mul-inclusion-Subgroup (group-Ab A) B {x} {y}

  preserves-zero-inclusion-Subgroup-Ab :
    preserves-zero-Ab (ab-Subgroup-Ab A B) A (map-inclusion-Subgroup-Ab A B)
  preserves-zero-inclusion-Subgroup-Ab =
    preserves-unit-inclusion-Subgroup (group-Ab A) B

  preserves-negatives-inclusion-Subgroup-Ab :
    preserves-negatives-Ab
      ( ab-Subgroup-Ab A B)
      ( A)
      ( map-inclusion-Subgroup-Ab A B)
  preserves-negatives-inclusion-Subgroup-Ab {x} =
    preserves-inverses-inclusion-Subgroup (group-Ab A) B {x}

  hom-inclusion-Subgroup-Ab : hom-Ab (ab-Subgroup-Ab A B) A
  hom-inclusion-Subgroup-Ab = hom-inclusion-Subgroup (group-Ab A) B
```

### Normal subgroups of an abelian group

```agda
Normal-Subgroup-Ab :
  {l1 : Level} (l2 : Level) (A : Ab l1) → UU (l1 ⊔ lsuc l2)
Normal-Subgroup-Ab l2 A = Normal-Subgroup l2 (group-Ab A)
```

## Properties

### Extensionality of the type of all subgroups of an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  has-same-elements-Subgroup-Ab :
    {l3 : Level} → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup-Ab =
    has-same-elements-Subgroup (group-Ab A) B

  extensionality-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → (B ＝ C) ≃ has-same-elements-Subgroup-Ab C
  extensionality-Subgroup-Ab =
    extensionality-Subgroup (group-Ab A) B

  refl-has-same-elements-Subgroup-Ab : has-same-elements-Subgroup-Ab B
  refl-has-same-elements-Subgroup-Ab =
    refl-has-same-elements-Subgroup (group-Ab A) B

  has-same-elements-eq-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → (B ＝ C) → has-same-elements-Subgroup-Ab C
  has-same-elements-eq-Subgroup-Ab =
    has-same-elements-eq-Subgroup (group-Ab A) B

  eq-has-same-elements-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → has-same-elements-Subgroup-Ab C → (B ＝ C)
  eq-has-same-elements-Subgroup-Ab =
    eq-has-same-elements-Subgroup (group-Ab A) B
```

### The containment relation of subgroups of abelian groups

```agda
leq-prop-Subgroup-Ab :
  {l1 l2 l3 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → Subgroup-Ab l3 A → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subgroup-Ab A = leq-prop-Subgroup (group-Ab A)

leq-Subgroup-Ab :
  {l1 l2 l3 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
leq-Subgroup-Ab A = leq-Subgroup (group-Ab A)

refl-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-reflexive-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
refl-leq-Subgroup-Ab A = refl-leq-Subgroup (group-Ab A)

transitive-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-transitive-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
transitive-leq-Subgroup-Ab A = transitive-leq-Subgroup (group-Ab A)

antisymmetric-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-antisymmetric-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
antisymmetric-leq-Subgroup-Ab A =
  antisymmetric-leq-Subgroup (group-Ab A)

Subgroup-Ab-Large-Preorder :
  {l1 : Level} (A : Ab l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Ab-Large-Preorder A =
  Subgroup-Large-Preorder (group-Ab A)

Subgroup-Ab-Preorder :
  {l1 : Level} (l2 : Level) (A : Ab l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Ab-Preorder l2 A = Subgroup-Preorder l2 (group-Ab A)

Subgroup-Ab-Large-Poset :
  {l1 : Level} (A : Ab l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Ab-Large-Poset A = Subgroup-Large-Poset (group-Ab A)

Subgroup-Ab-Poset :
  {l1 : Level} (l2 : Level) (A : Ab l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Ab-Poset l2 A = Subgroup-Poset l2 (group-Ab A)
```

### Every subgroup of an abelian group is normal

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  is-normal-Subgroup-Ab : is-normal-Subgroup (group-Ab A) B
  is-normal-Subgroup-Ab x y =
    is-closed-under-eq-Subgroup-Ab' A B
      ( is-in-subgroup-inclusion-Subgroup-Ab A B y)
      ( is-identity-conjugation-Ab A x (inclusion-Subgroup-Ab A B y))

  normal-subgroup-Subgroup-Ab : Normal-Subgroup-Ab l2 A
  pr1 normal-subgroup-Subgroup-Ab = B
  pr2 normal-subgroup-Subgroup-Ab = is-normal-Subgroup-Ab

  closure-property-Subgroup-Ab :
    {x y z : type-Ab A} →
    is-in-Subgroup-Ab A B y →
    is-in-Subgroup-Ab A B (add-Ab A x z) →
    is-in-Subgroup-Ab A B (add-Ab A (add-Ab A x y) z)
  closure-property-Subgroup-Ab =
    closure-property-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab)

  closure-property-Subgroup-Ab' :
    {x y z : type-Ab A} →
    is-in-Subgroup-Ab A B y →
    is-in-Subgroup-Ab A B (add-Ab A x z) →
    is-in-Subgroup-Ab A B (add-Ab A x (add-Ab A y z))
  closure-property-Subgroup-Ab' =
    closure-property-Normal-Subgroup'
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab)

  conjugation-Subgroup-Ab :
    type-Ab A → type-Subgroup-Ab A B → type-Subgroup-Ab A B
  conjugation-Subgroup-Ab =
    conjugation-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab)

  conjugation-Subgroup-Ab' :
    type-Ab A → type-Subgroup-Ab A B → type-Subgroup-Ab A B
  conjugation-Subgroup-Ab' =
    conjugation-Normal-Subgroup'
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab)
```

### Subgroups of abelian groups are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from a subgroup

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  sim-congruence-Subgroup-Ab : (x y : type-Ab A) → UU l2
  sim-congruence-Subgroup-Ab =
    sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  is-prop-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) → is-prop (sim-congruence-Subgroup-Ab x y)
  is-prop-sim-congruence-Subgroup-Ab =
    is-prop-sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  prop-congruence-Subgroup-Ab : (x y : type-Ab A) → Prop l2
  prop-congruence-Subgroup-Ab =
    prop-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)
```

#### The left equivalence relation obtained from a subgroup

```agda
  left-equivalence-relation-congruence-Subgroup-Ab :
    equivalence-relation l2 (type-Ab A)
  left-equivalence-relation-congruence-Subgroup-Ab =
    left-equivalence-relation-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  left-sim-congruence-Subgroup-Ab :
    type-Ab A → type-Ab A → UU l2
  left-sim-congruence-Subgroup-Ab =
    left-sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)
```

#### The left similarity relation of a subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) →
    sim-congruence-Subgroup-Ab x y →
    left-sim-congruence-Subgroup-Ab x y
  left-sim-sim-congruence-Subgroup-Ab =
    left-sim-sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  sim-left-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) →
    left-sim-congruence-Subgroup-Ab x y →
    sim-congruence-Subgroup-Ab x y
  sim-left-sim-congruence-Subgroup-Ab =
    sim-left-sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Subgroup-Ab :
    is-reflexive sim-congruence-Subgroup-Ab
  refl-congruence-Subgroup-Ab =
    refl-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  symmetric-congruence-Subgroup-Ab :
    is-symmetric sim-congruence-Subgroup-Ab
  symmetric-congruence-Subgroup-Ab =
    symmetric-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  transitive-congruence-Subgroup-Ab :
    is-transitive sim-congruence-Subgroup-Ab
  transitive-congruence-Subgroup-Ab =
    transitive-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  equivalence-relation-congruence-Subgroup-Ab :
    equivalence-relation l2 (type-Ab A)
  equivalence-relation-congruence-Subgroup-Ab =
    equivalence-relation-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  relate-same-elements-left-sim-congruence-Subgroup-Ab :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-Subgroup-Ab)
      ( left-equivalence-relation-congruence-Subgroup-Ab)
  relate-same-elements-left-sim-congruence-Subgroup-Ab =
    relate-same-elements-left-sim-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  add-congruence-Subgroup-Ab :
    is-congruence-Group
      ( group-Ab A)
      ( equivalence-relation-congruence-Subgroup-Ab)
  add-congruence-Subgroup-Ab =
    mul-congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  congruence-Subgroup-Ab : congruence-Ab l2 A
  congruence-Subgroup-Ab =
    congruence-Normal-Subgroup
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  neg-congruence-Subgroup-Ab :
    {x y : type-Ab A} →
    sim-congruence-Subgroup-Ab x y →
    sim-congruence-Subgroup-Ab (neg-Ab A x) (neg-Ab A y)
  neg-congruence-Subgroup-Ab =
    neg-congruence-Ab A congruence-Subgroup-Ab
```

#### The subgroup obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A)
  where

  subset-congruence-Ab : subset-Ab l2 A
  subset-congruence-Ab = prop-congruence-Ab A R (zero-Ab A)

  is-in-subset-congruence-Ab : (type-Ab A) → UU l2
  is-in-subset-congruence-Ab =
    is-in-subset-congruence-Group (group-Ab A) R

  contains-zero-subset-congruence-Ab :
    contains-zero-subset-Ab A subset-congruence-Ab
  contains-zero-subset-congruence-Ab =
    contains-unit-subset-congruence-Group (group-Ab A) R

  is-closed-under-addition-subset-congruence-Ab :
    is-closed-under-addition-subset-Ab A subset-congruence-Ab
  is-closed-under-addition-subset-congruence-Ab =
    is-closed-under-multiplication-subset-congruence-Group (group-Ab A) R

  is-closed-under-negatives-subset-congruence-Ab :
    is-closed-under-negatives-subset-Ab A subset-congruence-Ab
  is-closed-under-negatives-subset-congruence-Ab =
    is-closed-under-inverses-subset-congruence-Group (group-Ab A) R

  subgroup-congruence-Ab : Subgroup-Ab l2 A
  subgroup-congruence-Ab = subgroup-congruence-Group (group-Ab A) R

  is-normal-subgroup-congruence-Ab :
    is-normal-Subgroup (group-Ab A) subgroup-congruence-Ab
  is-normal-subgroup-congruence-Ab =
    is-normal-subgroup-congruence-Group (group-Ab A) R

  normal-subgroup-congruence-Ab : Normal-Subgroup l2 (group-Ab A)
  normal-subgroup-congruence-Ab =
    normal-subgroup-congruence-Group (group-Ab A) R
```

#### The subgroup obtained from the congruence relation of a subgroup `N` is `N` itself

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  has-same-elements-subgroup-congruence-Ab :
    has-same-elements-Subgroup-Ab A
      ( subgroup-congruence-Ab A
        ( congruence-Subgroup-Ab A B))
      ( B)
  has-same-elements-subgroup-congruence-Ab =
    has-same-elements-normal-subgroup-congruence-Group
      ( group-Ab A)
      ( normal-subgroup-Subgroup-Ab A B)

  is-retraction-subgroup-congruence-Ab :
    subgroup-congruence-Ab A (congruence-Subgroup-Ab A B) ＝ B
  is-retraction-subgroup-congruence-Ab =
    eq-has-same-elements-Subgroup-Ab A
      ( subgroup-congruence-Ab A (congruence-Subgroup-Ab A B))
      ( B)
      ( has-same-elements-subgroup-congruence-Ab)
```

#### The congruence relation of the subgroup obtained from a congruence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A)
  where

  relate-same-elements-congruence-subgroup-congruence-Ab :
    relate-same-elements-congruence-Ab A
      ( congruence-Subgroup-Ab A (subgroup-congruence-Ab A R))
      ( R)
  relate-same-elements-congruence-subgroup-congruence-Ab =
    relate-same-elements-congruence-normal-subgroup-congruence-Group
      ( group-Ab A)
      ( R)

  is-section-subgroup-congruence-Ab :
    congruence-Subgroup-Ab A (subgroup-congruence-Ab A R) ＝ R
  is-section-subgroup-congruence-Ab =
    eq-relate-same-elements-congruence-Ab A
      ( congruence-Subgroup-Ab A (subgroup-congruence-Ab A R))
      ( R)
      ( relate-same-elements-congruence-subgroup-congruence-Ab)
```

#### The equivalence of subgroups and congruence relations

```agda
module _
  {l1 l2 : Level} (A : Ab l1)
  where

  is-equiv-congruence-Subgroup-Ab :
    is-equiv (congruence-Subgroup-Ab {l1} {l2} A)
  is-equiv-congruence-Subgroup-Ab =
    is-equiv-is-invertible
      ( subgroup-congruence-Ab A)
      ( is-section-subgroup-congruence-Ab A)
      ( is-retraction-subgroup-congruence-Ab A)

  equiv-congruence-Subgroup-Ab :
    Subgroup-Ab l2 A ≃ congruence-Ab l2 A
  pr1 equiv-congruence-Subgroup-Ab =
    congruence-Subgroup-Ab A
  pr2 equiv-congruence-Subgroup-Ab =
    is-equiv-congruence-Subgroup-Ab

  is-equiv-subgroup-congruence-Ab :
    is-equiv (subgroup-congruence-Ab {l1} {l2} A)
  is-equiv-subgroup-congruence-Ab =
    is-equiv-is-invertible
      ( congruence-Subgroup-Ab A)
      ( is-retraction-subgroup-congruence-Ab A)
      ( is-section-subgroup-congruence-Ab A)

  equiv-subgroup-congruence-Ab :
    congruence-Ab l2 A ≃ Subgroup-Ab l2 A
  pr1 equiv-subgroup-congruence-Ab =
    subgroup-congruence-Ab A
  pr2 equiv-subgroup-congruence-Ab =
    is-equiv-subgroup-congruence-Ab
```
