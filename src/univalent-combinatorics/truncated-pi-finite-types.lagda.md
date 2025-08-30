# Truncated π-finite types

```agda
module univalent-combinatorics.truncated-pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-function-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

A type is
{{#concept "πₙ-finite" Disambiguation="type" Agda=is-truncated-π-finite Agda=Truncated-π-Finite-Type}},
or **n-truncated π-finite**, if it has
[finitely many connected components](univalent-combinatorics.finitely-many-connected-components.md),
all of its [homotopy groups](synthetic-homotopy-theory.homotopy-groups.md) up to
level `n` at all base points are finite, and all higher homotopy groups are
[trivial](group-theory.trivial-groups.md). Formally we define this condition
inductively:

- A π₀-finite type is a [finite type](univalent-combinatorics.finite-types.md).
- A πₙ₊₁-finite type is a type with
  [finitely many connected components](univalent-combinatorics.finitely-many-connected-components.md)
  whose [identity types](foundation-core.identity-types.md) are πₙ-finite.

## Definitions

### The πₙ-finiteness predicate

```agda
is-truncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-truncated-π-finite-Prop zero-ℕ X = is-finite-Prop X
is-truncated-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( has-finitely-many-connected-components-Prop X)
    ( Π-Prop X (λ x → Π-Prop X (λ y → is-truncated-π-finite-Prop k (x ＝ y))))

is-truncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-truncated-π-finite k A =
  type-Prop (is-truncated-π-finite-Prop k A)

is-prop-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-prop (is-truncated-π-finite k A)
is-prop-is-truncated-π-finite k {A} =
  is-prop-type-Prop (is-truncated-π-finite-Prop k A)

has-finitely-many-connected-components-is-truncated-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite k X → has-finitely-many-connected-components X
has-finitely-many-connected-components-is-truncated-π-finite zero-ℕ =
  has-finitely-many-connected-components-is-finite
has-finitely-many-connected-components-is-truncated-π-finite (succ-ℕ k) = pr1

is-truncated-π-finite-Id :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite (succ-ℕ k) X →
  (x y : X) → is-truncated-π-finite k (x ＝ y)
is-truncated-π-finite-Id k = pr2
```

### πₙ-finite types are n-truncated

```agda
is-trunc-is-truncated-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite k X → is-trunc (truncation-level-ℕ k) X
is-trunc-is-truncated-π-finite zero-ℕ = is-set-is-finite
is-trunc-is-truncated-π-finite (succ-ℕ k) H x y =
  is-trunc-is-truncated-π-finite k (is-truncated-π-finite-Id k H x y)
```

### πₙ-finite types are untruncated πₙ-finite

```agda
is-untruncated-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-truncated-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (_ , (is-set-is-finite H)))
    ( H)
pr1 (is-untruncated-π-finite-is-truncated-π-finite (succ-ℕ k) H) =
  has-finitely-many-connected-components-is-truncated-π-finite (succ-ℕ k) H
pr2 (is-untruncated-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y =
  is-untruncated-π-finite-is-truncated-π-finite k
    ( is-truncated-π-finite-Id k H x y)
```

### The subuniverse of πₙ-finite types

```agda
Truncated-π-Finite-Type : (l : Level) (k : ℕ) → UU (lsuc l)
Truncated-π-Finite-Type l k = Σ (UU l) (is-truncated-π-finite k)

module _
  {l : Level} (k : ℕ) (A : Truncated-π-Finite-Type l k)
  where

  type-Truncated-π-Finite-Type : UU l
  type-Truncated-π-Finite-Type = pr1 A

  is-truncated-π-finite-type-Truncated-π-Finite-Type :
    is-truncated-π-finite k type-Truncated-π-Finite-Type
  is-truncated-π-finite-type-Truncated-π-Finite-Type = pr2 A

  is-trunc-type-Truncated-π-Finite-Type :
    is-trunc (truncation-level-ℕ k) type-Truncated-π-Finite-Type
  is-trunc-type-Truncated-π-Finite-Type =
    is-trunc-is-truncated-π-finite k
      ( is-truncated-π-finite-type-Truncated-π-Finite-Type)

  is-untruncated-π-finite-type-Truncated-π-Finite-Type :
    is-untruncated-π-finite k type-Truncated-π-Finite-Type
  is-untruncated-π-finite-type-Truncated-π-Finite-Type =
    is-untruncated-π-finite-is-truncated-π-finite k
      ( is-truncated-π-finite-type-Truncated-π-Finite-Type)
```

## Properties

### Untruncated πₙ-finite n-truncated types are πₙ-finite

```agda
is-truncated-π-finite-is-untruncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-untruncated-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-untruncated-π-finite zero-ℕ H K =
  is-finite-is-untruncated-π-finite zero-ℕ H K
pr1 (is-truncated-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-truncated-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) x y =
  is-truncated-π-finite-is-untruncated-π-finite k
    ( H x y)
    ( is-untruncated-π-finite-Id k K x y)
```

### πₙ-finite types are closed under retracts

```agda
is-truncated-π-finite-retract :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A retract-of B → is-truncated-π-finite k B → is-truncated-π-finite k A
is-truncated-π-finite-retract zero-ℕ = is-finite-retract
pr1 (is-truncated-π-finite-retract (succ-ℕ k) r H) =
  has-finitely-many-connected-components-retract r
    ( has-finitely-many-connected-components-is-truncated-π-finite (succ-ℕ k) H)
pr2 (is-truncated-π-finite-retract (succ-ℕ k) r H) x y =
  is-truncated-π-finite-retract k
    ( retract-eq r x y)
    ( is-truncated-π-finite-Id k H
      ( inclusion-retract r x)
      ( inclusion-retract r y))
```

### πₙ-finite types are closed under equivalences

```agda
is-truncated-π-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-truncated-π-finite k B → is-truncated-π-finite k A
is-truncated-π-finite-equiv k e =
  is-truncated-π-finite-retract k (retract-equiv e)

is-truncated-π-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-truncated-π-finite k A → is-truncated-π-finite k B
is-truncated-π-finite-equiv' k e =
  is-truncated-π-finite-retract k (retract-inv-equiv e)
```

### Empty types are πₙ-finite

```agda
is-truncated-π-finite-empty : (k : ℕ) → is-truncated-π-finite k empty
is-truncated-π-finite-empty zero-ℕ = is-finite-empty
is-truncated-π-finite-empty (succ-ℕ k) =
  ( has-finitely-many-connected-components-empty , ind-empty)

empty-Truncated-π-Finite-Type : (k : ℕ) → Truncated-π-Finite-Type lzero k
empty-Truncated-π-Finite-Type k = (empty , is-truncated-π-finite-empty k)

is-truncated-π-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-truncated-π-finite k A
is-truncated-π-finite-is-empty zero-ℕ = is-finite-is-empty
is-truncated-π-finite-is-empty (succ-ℕ k) f =
  ( has-finitely-many-connected-components-is-empty f , ex-falso ∘ f)
```

### Contractible types are πₙ-finite

```agda
is-truncated-π-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-truncated-π-finite k A
is-truncated-π-finite-is-contr zero-ℕ =
  is-finite-is-contr
pr1 (is-truncated-π-finite-is-contr (succ-ℕ k) H) =
  has-finitely-many-connected-components-is-contr H
pr2 (is-truncated-π-finite-is-contr (succ-ℕ k) H) x y =
  is-truncated-π-finite-is-contr k (is-prop-is-contr H x y)

is-truncated-π-finite-unit : (k : ℕ) → is-truncated-π-finite k unit
is-truncated-π-finite-unit k =
  is-truncated-π-finite-is-contr k is-contr-unit

unit-Truncated-π-Finite-Type : (k : ℕ) → Truncated-π-Finite-Type lzero k
unit-Truncated-π-Finite-Type k =
  ( unit , is-truncated-π-finite-unit k)
```

### Coproducts of πₙ-finite types are πₙ-finite

```agda
is-truncated-π-finite-coproduct :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-truncated-π-finite k A → is-truncated-π-finite k B →
  is-truncated-π-finite k (A + B)
is-truncated-π-finite-coproduct k hA hB =
  is-truncated-π-finite-is-untruncated-π-finite k
    ( is-trunc-coproduct
      ( truncation-level-minus-two-ℕ k)
      ( is-trunc-is-truncated-π-finite k hA)
      ( is-trunc-is-truncated-π-finite k hB))
    ( is-untruncated-π-finite-coproduct k
      ( is-untruncated-π-finite-is-truncated-π-finite k hA)
      ( is-untruncated-π-finite-is-truncated-π-finite k hB))

coproduct-Truncated-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) →
  Truncated-π-Finite-Type l1 k →
  Truncated-π-Finite-Type l2 k →
  Truncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (coproduct-Truncated-π-Finite-Type k A B) =
  type-Truncated-π-Finite-Type k A + type-Truncated-π-Finite-Type k B
pr2 (coproduct-Truncated-π-Finite-Type k A B) =
  is-truncated-π-finite-coproduct k
    ( is-truncated-π-finite-type-Truncated-π-Finite-Type k A)
    ( is-truncated-π-finite-type-Truncated-π-Finite-Type k B)
```

### `Maybe A` of any πₙ-finite type `A` is πₙ-finite

```agda
is-truncated-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-truncated-π-finite k (Maybe A)
is-truncated-π-finite-Maybe k H =
  is-truncated-π-finite-coproduct k H (is-truncated-π-finite-unit k)

Maybe-Truncated-π-Finite-Type :
  {l : Level} (k : ℕ) →
  Truncated-π-Finite-Type l k → Truncated-π-Finite-Type l k
Maybe-Truncated-π-Finite-Type k (A , H) =
  ( Maybe A , is-truncated-π-finite-Maybe k H)
```

### Any standard finite type is πₙ-finite

```agda
is-truncated-π-finite-Fin : (k n : ℕ) → is-truncated-π-finite k (Fin n)
is-truncated-π-finite-Fin k zero-ℕ = is-truncated-π-finite-empty k
is-truncated-π-finite-Fin k (succ-ℕ n) =
  is-truncated-π-finite-Maybe k (is-truncated-π-finite-Fin k n)

Fin-Truncated-π-Finite-Type : (k : ℕ) (n : ℕ) → Truncated-π-Finite-Type lzero k
Fin-Truncated-π-Finite-Type k n = (Fin n , is-truncated-π-finite-Fin k n)
```

### Any type equipped with a counting is πₙ-finite

```agda
is-truncated-π-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-truncated-π-finite k A
is-truncated-π-finite-count k (n , e) =
  is-truncated-π-finite-equiv' k e (is-truncated-π-finite-Fin k n)
```

### Any finite type is πₙ-finite

```agda
is-truncated-π-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-truncated-π-finite k A
is-truncated-π-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-truncated-π-finite-Prop k A)
    ( is-truncated-π-finite-count k)

truncated-π-finite-type-Finite-Type :
  {l : Level} (k : ℕ) → Finite-Type l → Truncated-π-Finite-Type l k
truncated-π-finite-type-Finite-Type k A =
  ( type-Finite-Type A ,
    is-truncated-π-finite-is-finite k (is-finite-type-Finite-Type A))
```

### πₙ-finite sets are finite

```agda
is-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-set A → is-truncated-π-finite k A → is-finite A
is-finite-is-truncated-π-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-truncated-π-finite k K)
```

### πₙ-finite types are πₙ₊₁-finite

```agda
is-truncated-π-finite-succ-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-truncated-π-finite (succ-ℕ k) A
is-truncated-π-finite-succ-is-truncated-π-finite zero-ℕ =
  is-truncated-π-finite-is-finite 1
is-truncated-π-finite-succ-is-truncated-π-finite (succ-ℕ k) (H , K) =
  ( H , (λ x y → is-truncated-π-finite-succ-is-truncated-π-finite k (K x y)))
```

### The type of all `n`-element types in `UU l` is π₁-finite

```agda
is-truncated-π-finite-Type-With-Cardinality-ℕ :
  {l : Level} (n : ℕ) → is-truncated-π-finite 1 (Type-With-Cardinality-ℕ l n)
is-truncated-π-finite-Type-With-Cardinality-ℕ n =
  is-truncated-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Type-With-Cardinality-ℕ n)
    ( is-untruncated-π-finite-Type-With-Cardinality-ℕ 1 n)

Type-With-Cardinality-ℕ-Truncated-π-Finite-Type :
  (l : Level) (n : ℕ) → Truncated-π-Finite-Type (lsuc l) 1
Type-With-Cardinality-ℕ-Truncated-π-Finite-Type l n =
  ( Type-With-Cardinality-ℕ l n ,
    is-truncated-π-finite-Type-With-Cardinality-ℕ n)
```

### Finite products of πₙ-finite types are πₙ-finite

```agda
is-truncated-π-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-truncated-π-finite k (B a)) →
  is-truncated-π-finite k ((a : A) → B a)
is-truncated-π-finite-Π k hA hB =
  is-truncated-π-finite-is-untruncated-π-finite k
    ( is-trunc-Π (truncation-level-ℕ k) (is-trunc-is-truncated-π-finite k ∘ hB))
    ( is-untruncated-π-finite-Π k hA
      ( is-untruncated-π-finite-is-truncated-π-finite k ∘ hB))

finite-Π-Truncated-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) (A : Finite-Type l1)
  (B : type-Finite-Type A → Truncated-π-Finite-Type l2 k) →
  Truncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (finite-Π-Truncated-π-Finite-Type k A B) =
  (x : type-Finite-Type A) → (type-Truncated-π-Finite-Type k (B x))
pr2 (finite-Π-Truncated-π-Finite-Type k A B) =
  is-truncated-π-finite-Π k
    ( is-finite-type-Finite-Type A)
      ( λ x → is-truncated-π-finite-type-Truncated-π-Finite-Type k (B x))
```

### Dependent sums of πₙ-finite types are πₙ-finite

```agda
is-truncated-π-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-truncated-π-finite k A → ((a : A) → is-truncated-π-finite k (B a)) →
  is-truncated-π-finite k (Σ A B)
is-truncated-π-finite-Σ k hA hB =
  is-truncated-π-finite-is-untruncated-π-finite k
    ( is-trunc-Σ
      ( is-trunc-is-truncated-π-finite k hA)
      ( is-trunc-is-truncated-π-finite k ∘ hB))
    ( is-untruncated-π-finite-Σ k
      ( is-untruncated-π-finite-is-truncated-π-finite (succ-ℕ k)
        ( is-truncated-π-finite-succ-is-truncated-π-finite k hA))
      ( is-untruncated-π-finite-is-truncated-π-finite k ∘ hB))

Σ-Truncated-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) (A : Truncated-π-Finite-Type l1 k)
  (B : type-Truncated-π-Finite-Type k A → Truncated-π-Finite-Type l2 k) →
  Truncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (Σ-Truncated-π-Finite-Type k A B) =
  Σ (type-Truncated-π-Finite-Type k A) (type-Truncated-π-Finite-Type k ∘ B)
pr2 (Σ-Truncated-π-Finite-Type k A B) =
  is-truncated-π-finite-Σ k
    ( is-truncated-π-finite-type-Truncated-π-Finite-Type k A)
    ( is-truncated-π-finite-type-Truncated-π-Finite-Type k ∘ B)
```

## See also

- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
