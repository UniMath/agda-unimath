# Integer multiples of elements in abelian groups

```agda
module group-theory.integer-multiples-of-elements-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.multiples-of-elements-abelian-groups
```

</details>

## Idea

The integer
{{#concept "multiplication" Disambiguation="integer multiplication of elements of abelian groups" Agda=integer-multiple-Ab}}
on an [abelian group](group-theory.abelian-groups.md) is the map `k x ↦ kx`,
which is defined by [iteratively](foundation.iterating-automorphisms.md) adding
`x` with itself an [integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively adding `g`

```agda
module _
  {l : Level} (A : Ab l)
  where

  iterative-addition-by-element-Ab :
    type-Ab A → ℤ → type-Ab A → type-Ab A
  iterative-addition-by-element-Ab =
    iterative-multiplication-by-element-Group (group-Ab A)
```

### Integer multiples of abelian group elements

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-Ab : ℤ → type-Ab A → type-Ab A
  integer-multiple-Ab = integer-power-Group (group-Ab A)
```

### The predicate of being an integer multiple of an element in an abelian group

We say that an element `y` **is an integer multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) an integer `k` such that
`kx ＝ y`.

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-integer-multiple-of-element-prop-Ab :
    (x y : type-Ab A) → Prop l
  is-integer-multiple-of-element-prop-Ab =
    is-integer-power-of-element-prop-Group (group-Ab A)

  is-integer-multiple-of-element-Ab :
    (x y : type-Ab A) → UU l
  is-integer-multiple-of-element-Ab =
    is-integer-power-of-element-Group (group-Ab A)

  is-prop-is-integer-multiple-of-element-Ab :
    (x y : type-Ab A) →
    is-prop (is-integer-multiple-of-element-Ab x y)
  is-prop-is-integer-multiple-of-element-Ab =
    is-prop-is-integer-power-of-element-Group (group-Ab A)
```

## Properties

### Associativity of iterated addition by a group element

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  associative-iterative-addition-by-element-Ab :
    (k : ℤ) (h1 h2 : type-Ab A) →
    iterative-addition-by-element-Ab A a k (add-Ab A h1 h2) ＝
    add-Ab A (iterative-addition-by-element-Ab A a k h1) h2
  associative-iterative-addition-by-element-Ab =
    associative-iterative-multiplication-by-element-Group (group-Ab A) a
```

### `integer-multiple-Ab A (int-ℕ n) a ＝ multiple-Ab A n a`

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-int-Ab :
    (n : ℕ) (a : type-Ab A) →
    integer-multiple-Ab A (int-ℕ n) a ＝ multiple-Ab A n a
  integer-multiple-int-Ab = integer-power-int-Group (group-Ab A)

  integer-multiple-in-pos-Ab :
    (n : ℕ) (a : type-Ab A) →
    integer-multiple-Ab A (in-pos-ℤ n) a ＝
    multiple-Ab A (succ-ℕ n) a
  integer-multiple-in-pos-Ab =
    integer-power-in-pos-Group (group-Ab A)

  integer-multiple-in-neg-Ab :
    (n : ℕ) (a : type-Ab A) →
    integer-multiple-Ab A (in-neg-ℤ n) a ＝
    neg-Ab A (multiple-Ab A (succ-ℕ n) a)
  integer-multiple-in-neg-Ab =
    integer-power-in-neg-Group (group-Ab A)
```

### The integer multiple `0x` is `0`

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  integer-multiple-zero-Ab :
    integer-multiple-Ab A zero-ℤ a ＝ zero-Ab A
  integer-multiple-zero-Ab =
    integer-power-zero-Group (group-Ab A) a
```

### `1x ＝ x`

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  integer-multiple-one-Ab :
    integer-multiple-Ab A one-ℤ a ＝ a
  integer-multiple-one-Ab =
    integer-power-one-Group (group-Ab A) a
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  integer-multiple-neg-one-Ab :
    integer-multiple-Ab A neg-one-ℤ a ＝ neg-Ab A a
  integer-multiple-neg-one-Ab =
    integer-power-neg-one-Group (group-Ab A) a
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  distributive-integer-multiple-add-Ab :
    (x y : ℤ) →
    integer-multiple-Ab A (x +ℤ y) a ＝
    add-Ab A
      ( integer-multiple-Ab A x a)
      ( integer-multiple-Ab A y a)
  distributive-integer-multiple-add-Ab =
    distributive-integer-power-add-Group (group-Ab A) a
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-neg-Ab :
    (k : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (neg-ℤ k) x ＝ neg-Ab A (integer-multiple-Ab A k x)
  integer-multiple-neg-Ab =
    integer-power-neg-Group (group-Ab A)
```

### `(k + 1)x = kx + x` and `(k+1)x = x + kx`

```agda
module _
  {l1 : Level} (A : Ab l1)
  where

  integer-multiple-succ-Ab :
    (k : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (succ-ℤ k) x ＝
    add-Ab A (integer-multiple-Ab A k x) x
  integer-multiple-succ-Ab =
    integer-power-succ-Group (group-Ab A)

  integer-multiple-succ-Ab' :
    (k : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (succ-ℤ k) x ＝
    add-Ab A x (integer-multiple-Ab A k x)
  integer-multiple-succ-Ab' =
    integer-power-succ-Group' (group-Ab A)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1 : Level} (A : Ab l1)
  where

  integer-multiple-pred-Ab :
    (k : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (pred-ℤ k) x ＝
    right-subtraction-Ab A (integer-multiple-Ab A k x) x
  integer-multiple-pred-Ab =
    integer-power-pred-Group (group-Ab A)

  integer-multiple-pred-Ab' :
    (k : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (pred-ℤ k) x ＝
    left-subtraction-Ab A x (integer-multiple-Ab A k x)
  integer-multiple-pred-Ab' =
    integer-power-pred-Group' (group-Ab A)
```

### `k0 ＝ 0`

```agda
module _
  {l : Level} (A : Ab l)
  where

  right-zero-law-integer-multiple-Ab :
    (k : ℤ) → integer-multiple-Ab A k (zero-Ab A) ＝ zero-Ab A
  right-zero-law-integer-multiple-Ab =
    integer-power-unit-Group (group-Ab A)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (A : Ab l)
  where

  left-distributive-integer-multiple-add-Ab :
    (k : ℤ) (x y : type-Ab A) →
    integer-multiple-Ab A k (add-Ab A x y) ＝
    add-Ab A (integer-multiple-Ab A k x) (integer-multiple-Ab A k y)
  left-distributive-integer-multiple-add-Ab k x y =
    distributive-integer-power-mul-Group
      ( group-Ab A)
      ( k)
      ( x)
      ( y)
      ( commutative-add-Ab A x y)
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {l : Level} (A : Ab l) (k : ℤ)
  where

  hom-integer-multiple-Ab : hom-Ab A A
  pr1 hom-integer-multiple-Ab =
    integer-multiple-Ab A k
  pr2 hom-integer-multiple-Ab {x} {y} =
    left-distributive-integer-multiple-add-Ab A k x y
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-mul-Ab :
    (k l : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A (k *ℤ l) x ＝
    integer-multiple-Ab A k (integer-multiple-Ab A l x)
  integer-multiple-mul-Ab k l x =
    ( ap (λ u → integer-multiple-Ab A u x) (commutative-mul-ℤ k l)) ∙
    ( integer-power-mul-Group (group-Ab A) l k x)

  swap-integer-multiple-Ab :
    (k l : ℤ) (x : type-Ab A) →
    integer-multiple-Ab A k (integer-multiple-Ab A l x) ＝
    integer-multiple-Ab A l (integer-multiple-Ab A k x)
  swap-integer-multiple-Ab k l x =
    ( inv (integer-multiple-mul-Ab k l x)) ∙
    ( ap (λ t → integer-multiple-Ab A t x) (commutative-mul-ℤ k l)) ∙
    ( integer-multiple-mul-Ab l k x)
```

### Abelian group homomorphisms preserve integer multiples

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B)
  where

  preserves-integer-multiples-hom-Ab :
    (k : ℤ) (x : type-Ab A) →
    map-hom-Ab A B f (integer-multiple-Ab A k x) ＝
    integer-multiple-Ab B k (map-hom-Ab A B f x)
  preserves-integer-multiples-hom-Ab =
    preserves-integer-powers-hom-Group (group-Ab A) (group-Ab B) f

module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B)
  where

  eq-integer-multiple-hom-Ab :
    (g : hom-Ab A B) (k : ℤ) (x : type-Ab A) →
    ( map-hom-Ab A B f x ＝ map-hom-Ab A B g x) →
    ( map-hom-Ab A B f (integer-multiple-Ab A k x) ＝
      map-hom-Ab A B g (integer-multiple-Ab A k x))
  eq-integer-multiple-hom-Ab =
    eq-integer-power-hom-Group (group-Ab A) (group-Ab B) f
```
