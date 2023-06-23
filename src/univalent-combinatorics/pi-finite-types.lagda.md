# π-finite types

```agda
module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is `π_n`-finite if it has finitely many connected components and all of
its homotopy groups up to level `n` at all base points are finite.

## Definition

### Locally finite types

```agda
is-locally-finite-Prop :
  {l : Level} → UU l → Prop l
is-locally-finite-Prop A =
  Π-Prop A (λ x → Π-Prop A (λ y → is-finite-Prop (Id x y)))

is-locally-finite : {l : Level} → UU l → UU l
is-locally-finite A = type-Prop (is-locally-finite-Prop A)

is-prop-is-locally-finite :
  {l : Level} (A : UU l) → is-prop (is-locally-finite A)
is-prop-is-locally-finite A = is-prop-type-Prop (is-locally-finite-Prop A)
```

### Truncated π-finite types

```agda
is-truncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-truncated-π-finite-Prop zero-ℕ X = is-finite-Prop X
is-truncated-π-finite-Prop (succ-ℕ k) X =
  prod-Prop
    ( is-finite-Prop (type-trunc-Set X))
    ( Π-Prop X
      ( λ x → Π-Prop X (λ y → is-truncated-π-finite-Prop k (Id x y))))

is-truncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-truncated-π-finite k A =
  type-Prop (is-truncated-π-finite-Prop k A)
```

### Types with finitely many connected components

```agda
has-finite-connected-components-Prop : {l : Level} → UU l → Prop l
has-finite-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finite-connected-components : {l : Level} → UU l → UU l
has-finite-connected-components A =
  type-Prop (has-finite-connected-components-Prop A)

number-of-connected-components :
  {l : Level} {X : UU l} → has-finite-connected-components X → ℕ
number-of-connected-components H = number-of-elements-is-finite H

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finite-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H =
  mere-equiv-is-finite H
```

### π-finite types

```agda
is-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-π-finite-Prop zero-ℕ X = has-finite-connected-components-Prop X
is-π-finite-Prop (succ-ℕ k) X =
  prod-Prop ( is-π-finite-Prop zero-ℕ X)
            ( Π-Prop X
              ( λ x → Π-Prop X (λ y → is-π-finite-Prop k (Id x y))))

is-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-π-finite k X = type-Prop (is-π-finite-Prop k X)

is-prop-is-π-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-π-finite k X)
is-prop-is-π-finite k X =
  is-prop-type-Prop (is-π-finite-Prop k X)

π-Finite : (l : Level) (k : ℕ) → UU (lsuc l)
π-Finite l k = Σ (UU l) (is-π-finite k)

type-π-Finite :
  {l : Level} (k : ℕ) → π-Finite l k → UU l
type-π-Finite k = pr1

is-π-finite-type-π-Finite :
  {l : Level} (k : ℕ) (A : π-Finite l k) →
  is-π-finite k (type-π-Finite {l} k A)
is-π-finite-type-π-Finite k = pr2
```

## Properties

### Locally finite types are closed under equivalences

```agda
is-locally-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite B → is-locally-finite A
is-locally-finite-equiv e f x y =
  is-finite-equiv' (equiv-ap e x y) (f (map-equiv e x) (map-equiv e y))

is-locally-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite A → is-locally-finite B
is-locally-finite-equiv' e = is-locally-finite-equiv (inv-equiv e)
```

### types with decidable equality are locally finite

```agda
is-locally-finite-has-decidable-equality :
  {l1 : Level} {A : UU l1} → has-decidable-equality A → is-locally-finite A
is-locally-finite-has-decidable-equality d x y = is-finite-eq d
```

### Any proposition is locally finite

```agda
is-locally-finite-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → is-locally-finite A
is-locally-finite-is-prop H x y = is-finite-is-contr (H x y)
```

### Any contractible type is locally finite

```agda
is-locally-finite-is-contr :
  {l1 : Level} {A : UU l1} → is-contr A → is-locally-finite A
is-locally-finite-is-contr H =
  is-locally-finite-is-prop (is-prop-is-contr H)

is-locally-finite-unit : is-locally-finite unit
is-locally-finite-unit = is-locally-finite-is-contr is-contr-unit
```

### Any empty type is locally finite

```agda
is-locally-finite-is-empty :
  {l1 : Level} {A : UU l1} → is-empty A → is-locally-finite A
is-locally-finite-is-empty H = is-locally-finite-is-prop (λ x → ex-falso (H x))

is-locally-finite-empty : is-locally-finite empty
is-locally-finite-empty = is-locally-finite-is-empty id
```

### π-finite types are closed under equivalences

```agda
is-π-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-π-finite k B → is-π-finite k A
is-π-finite-equiv zero-ℕ e H =
  is-finite-equiv' (equiv-trunc-Set e) H
pr1 (is-π-finite-equiv (succ-ℕ k) e H) = is-π-finite-equiv zero-ℕ e (pr1 H)
pr2 (is-π-finite-equiv (succ-ℕ k) e H) a b =
  is-π-finite-equiv k
    ( equiv-ap e a b)
    ( pr2 H (map-equiv e a) (map-equiv e b))

is-π-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-π-finite k A → is-π-finite k B
is-π-finite-equiv' k e = is-π-finite-equiv k (inv-equiv e)
```

### The empty type is π-finite

```agda
is-π-finite-empty : (k : ℕ) → is-π-finite k empty
is-π-finite-empty zero-ℕ =
  is-finite-equiv equiv-unit-trunc-empty-Set is-finite-empty
pr1 (is-π-finite-empty (succ-ℕ k)) = is-π-finite-empty zero-ℕ
pr2 (is-π-finite-empty (succ-ℕ k)) = ind-empty

empty-π-Finite : (k : ℕ) → π-Finite lzero k
pr1 (empty-π-Finite k) = empty
pr2 (empty-π-Finite k) = is-π-finite-empty k
```

### Any empty type is π-finite

```agda
is-π-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-π-finite k A
is-π-finite-is-empty zero-ℕ f =
  is-finite-is-empty (is-empty-trunc-Set f)
pr1 (is-π-finite-is-empty (succ-ℕ k) f) = is-π-finite-is-empty zero-ℕ f
pr2 (is-π-finite-is-empty (succ-ℕ k) f) a = ex-falso (f a)
```

### Any contractible type is π-finite

```agda
is-π-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-π-finite k A
is-π-finite-is-contr zero-ℕ H =
  is-finite-is-contr (is-contr-trunc-Set H)
pr1 (is-π-finite-is-contr (succ-ℕ k) H) = is-π-finite-is-contr zero-ℕ H
pr2 (is-π-finite-is-contr (succ-ℕ k) H) x y =
  is-π-finite-is-contr k ( is-prop-is-contr H x y)
```

### The unit type is π-finite

```agda
is-π-finite-unit :
  (k : ℕ) → is-π-finite k unit
is-π-finite-unit k = is-π-finite-is-contr k is-contr-unit

unit-π-Finite : (k : ℕ) → π-Finite lzero k
pr1 (unit-π-Finite k) = unit
pr2 (unit-π-Finite k) = is-π-finite-unit k
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coprod :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-π-finite k A → is-π-finite k B →
  is-π-finite k (A + B)
is-π-finite-coprod zero-ℕ H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coprod-Set _ _)
    ( is-finite-coprod H K)
pr1 (is-π-finite-coprod (succ-ℕ k) H K) =
  is-π-finite-coprod zero-ℕ (pr1 H) (pr1 K)
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inl x) (inl y) =
  is-π-finite-equiv k
    ( compute-eq-coprod-inl-inl x y)
    ( pr2 H x y)
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inl x) (inr y) =
  is-π-finite-equiv k
    ( compute-eq-coprod-inl-inr x y)
    ( is-π-finite-empty k)
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inr x) (inl y) =
  is-π-finite-equiv k
    ( compute-eq-coprod-inr-inl x y)
    ( is-π-finite-empty k)
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inr x) (inr y) =
  is-π-finite-equiv k
    ( compute-eq-coprod-inr-inr x y)
    ( pr2 K x y)

coprod-π-Finite :
  {l1 l2 : Level} (k : ℕ) →
  π-Finite l1 k → π-Finite l2 k → π-Finite (l1 ⊔ l2) k
pr1 (coprod-π-Finite k A B) = (type-π-Finite k A + type-π-Finite k B)
pr2 (coprod-π-Finite k A B) =
  is-π-finite-coprod k
    ( is-π-finite-type-π-Finite k A)
    ( is-π-finite-type-π-Finite k B)
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
Maybe-π-Finite :
  {l : Level} (k : ℕ) → π-Finite l k → π-Finite l k
Maybe-π-Finite k A =
  coprod-π-Finite k A (unit-π-Finite k)

is-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → is-π-finite k (Maybe A)
is-π-finite-Maybe k H =
  is-π-finite-coprod k H (is-π-finite-unit k)
```

### Any stanadard finite type is π-finite

```agda
is-π-finite-Fin :
  (k n : ℕ) → is-π-finite k (Fin n)
is-π-finite-Fin k zero-ℕ =
  is-π-finite-empty k
is-π-finite-Fin k (succ-ℕ n) =
  is-π-finite-Maybe k (is-π-finite-Fin k n)

Fin-π-Finite : (k : ℕ) (n : ℕ) → π-Finite lzero k
pr1 (Fin-π-Finite k n) = Fin n
pr2 (Fin-π-Finite k n) = is-π-finite-Fin k n
```

### Any type equipped with a counting is π-finite

```agda
is-π-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-π-finite k A
is-π-finite-count k (pair n e) =
  is-π-finite-equiv' k e (is-π-finite-Fin k n)
```

### Any finite type is π-finite

```agda
is-π-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-π-finite k A
is-π-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-π-finite-Prop k A)
    ( is-π-finite-count k)

π-finite-𝔽 : {l : Level} (k : ℕ) → 𝔽 l → π-Finite l k
pr1 (π-finite-𝔽 k A) = type-𝔽 A
pr2 (π-finite-𝔽 k A) = is-π-finite-is-finite k (is-finite-type-𝔽 A)
```

### Any 0-connected type has finitely many connected components

```agda
has-finite-connected-components-is-0-connected :
  {l : Level} {A : UU l} →
  is-0-connected A → has-finite-connected-components A
has-finite-connected-components-is-0-connected C =
  is-finite-is-contr C
```

### The type of all `n`-element types in `UU l` is π-finite

```agda
is-π-finite-UU-Fin :
  {l : Level} (k n : ℕ) → is-π-finite k (UU-Fin l n)
is-π-finite-UU-Fin zero-ℕ n =
  has-finite-connected-components-is-0-connected
    ( is-0-connected-UU-Fin n)
pr1 (is-π-finite-UU-Fin (succ-ℕ k) n) = is-π-finite-UU-Fin zero-ℕ n
pr2 (is-π-finite-UU-Fin (succ-ℕ k) n) x y =
  is-π-finite-equiv k
    ( equiv-equiv-eq-UU-Fin n x y)
    ( is-π-finite-is-finite k
      ( is-finite-≃
        ( is-finite-has-finite-cardinality (pair n (pr2 x)))
        ( is-finite-has-finite-cardinality (pair n (pr2 y)))))

is-finite-has-finite-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finite-connected-components A → is-finite A
is-finite-has-finite-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (pair _ H))

has-finite-connected-components-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → has-finite-connected-components A
has-finite-connected-components-is-π-finite zero-ℕ H = H
has-finite-connected-components-is-π-finite (succ-ℕ k) H = pr1 H

is-π-finite-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite k A
is-π-finite-is-π-finite-succ-ℕ zero-ℕ H =
  has-finite-connected-components-is-π-finite 1 H
pr1 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) =
  has-finite-connected-components-is-π-finite (succ-ℕ (succ-ℕ k)) H
pr2 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) x y =
  is-π-finite-is-π-finite-succ-ℕ k (pr2 H x y)

is-π-finite-one-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite 1 A
is-π-finite-one-is-π-finite-succ-ℕ zero-ℕ H = H
is-π-finite-one-is-π-finite-succ-ℕ (succ-ℕ k) H =
  is-π-finite-one-is-π-finite-succ-ℕ k
    ( is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H)

is-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-π-finite k A → is-finite A
is-finite-is-π-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (pair _ H))
    ( has-finite-connected-components-is-π-finite k K)

is-truncated-π-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-π-finite zero-ℕ H K =
  is-finite-is-π-finite zero-ℕ H K
pr1 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) x y =
  is-truncated-π-finite-is-π-finite k (H x y) (pr2 K x y)

is-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-π-finite k A
is-π-finite-is-truncated-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (pair _ (is-set-is-finite H)))
    ( H)
pr1 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) = pr1 H
pr2 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y =
  is-π-finite-is-truncated-π-finite k (pr2 H x y)
```

### Proposition 1.5

#### The dependent product of locally finite types

```agda
is-locally-finite-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-locally-finite A → is-locally-finite B → is-locally-finite (A × B)
is-locally-finite-prod f g x y =
  is-finite-equiv
    ( equiv-eq-pair x y)
    ( is-finite-prod (f (pr1 x) (pr1 y)) (g (pr2 x) (pr2 y)))

is-locally-finite-Π-Fin :
  {l1 : Level} (k : ℕ) {B : Fin k → UU l1} →
  ((x : Fin k) → is-locally-finite (B x)) →
  is-locally-finite ((x : Fin k) → B x)
is-locally-finite-Π-Fin {l1} zero-ℕ {B} f =
  is-locally-finite-is-contr (dependent-universal-property-empty' B)
is-locally-finite-Π-Fin {l1} (succ-ℕ k) {B} f =
  is-locally-finite-equiv
    ( equiv-dependent-universal-property-coprod B)
    ( is-locally-finite-prod
      ( is-locally-finite-Π-Fin k (λ x → f (inl x)))
      ( is-locally-finite-equiv
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( f (inr star))))

is-locally-finite-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π-count {l1} {l2} {A} {B} (pair k e) g =
  is-locally-finite-equiv
    ( equiv-precomp-Π e B)
    ( is-locally-finite-Π-Fin k (λ x → g (map-equiv e x)))

is-locally-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π {l1} {l2} {A} {B} f g =
  apply-universal-property-trunc-Prop f
    ( is-locally-finite-Prop ((x : A) → B x))
    ( λ e → is-locally-finite-Π-count e g)
```

#### Finite products of π-finite types

```agda
is-π-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-π-finite k (B a)) →
  is-π-finite k ((a : A) → B a)
is-π-finite-Π zero-ℕ {A} {B} H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-Π-is-finite-Set B H)
    ( is-finite-Π H K)
pr1 (is-π-finite-Π (succ-ℕ k) H K) = is-π-finite-Π zero-ℕ H (λ a → pr1 (K a))
pr2 (is-π-finite-Π (succ-ℕ k) H K) f g =
  is-π-finite-equiv k
    ( equiv-funext)
    ( is-π-finite-Π k H (λ a → pr2 (K a) (f a) (g a)))

π-Finite-Π :
  {l1 l2 : Level} (k : ℕ) (A : 𝔽 l1) (B : type-𝔽 A → π-Finite l2 k) →
  π-Finite (l1 ⊔ l2) k
pr1 (π-Finite-Π k A B) =
  (x : type-𝔽 A) → (type-π-Finite k (B x))
pr2 (π-Finite-Π k A B) =
  is-π-finite-Π k
    ( is-finite-type-𝔽 A)
    ( λ x → is-π-finite-type-π-Finite k (B x))
```

### Proposition 1.6

```agda
is-locally-finite-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-locally-finite A → ((x : A) → is-locally-finite (B x)) →
  is-locally-finite (Σ A B)
is-locally-finite-Σ {B = B} H K (pair x y) (pair x' y') =
  is-finite-equiv'
    ( equiv-pair-eq-Σ (pair x y) (pair x' y'))
    ( is-finite-Σ (H x x') (λ p → K x' (tr B p y) y'))
```

### Proposition 1.7

```agda
has-finite-connected-components-Σ-is-0-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-0-connected A → is-π-finite 1 A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ-is-0-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-0-connected C)
    ( is-π-finite-Prop zero-ℕ (Σ A B))
    ( α)

  where
  α : A → is-π-finite zero-ℕ (Σ A B)
  α a =
    is-finite-codomain
      ( K a)
      ( is-surjective-map-trunc-Set
        ( fiber-inclusion B a)
        ( is-surjective-fiber-inclusion C a))
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x →
          set-Prop
            ( Π-Prop
              ( type-trunc-Set (Σ A B))
              ( λ y → is-decidable-Prop (Id-Prop (trunc-Set (Σ A B)) x y))))
        ( β))

    where
    β : (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
        is-decidable (Id (unit-trunc-Set x) v)
    β (pair x y) =
      apply-dependent-universal-property-trunc-Set'
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (pair x y)) u)))
        ( γ)

      where
      γ : (v : Σ A B) →
          is-decidable (Id (unit-trunc-Set (pair x y)) (unit-trunc-Set v))
      γ (pair x' y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( pair x y)
            ( pair x' y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (pair x y) (pair x' y')))
              ( δ))

        where
        δ : Id a x → is-decidable (mere-eq (pair x y) (pair x' y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (pair a y) (pair x' y')))
            ( ε)

          where
          ε : Id a x' → is-decidable (mere-eq (pair x y) (pair x' y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( pr2 H a a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))

            where
            ℙ : is-contr
                ( Σ ( type-hom-Set (trunc-Set (Id a a)) (Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ → trunc-Prop (Id (tr B ω₁ y) y'))))
            ℙ = universal-property-trunc-Set
                ( Id a a)
                ( Prop-Set _)
                ( λ ω → trunc-Prop (Id (tr B ω y) y'))
            P : type-trunc-Set (Id a a) → Prop _
            P = pr1 (center ℙ)
            compute-P :
              ( ω : Id a a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (Id (tr B ω y) y')
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))
            d : (t : type-trunc-Set (Id a a)) → is-decidable (type-Prop (P t))
            d = apply-dependent-universal-property-trunc-Set'
                ( λ t → set-Prop (is-decidable-Prop (P t)))
                ( λ ω →
                  is-decidable-equiv'
                    ( inv-equiv (compute-P ω))
                    ( is-decidable-equiv'
                      ( is-effective-unit-trunc-Set (B a) (tr B ω y) y')
                      ( has-decidable-equality-is-finite
                        ( K a)
                        ( unit-trunc-Set (tr B ω y))
                        ( unit-trunc-Set y'))))
            f : type-hom-Prop
                ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                ( mere-eq-Prop {A = Σ A B} (pair a y) (pair a y'))
            f t = apply-universal-property-trunc-Prop t
                    ( mere-eq-Prop (pair a y) (pair a y'))
                      λ { (pair u v) →
                          apply-dependent-universal-property-trunc-Set'
                            ( λ u' →
                              hom-Set
                                ( set-Prop (P u'))
                                ( set-Prop
                                  ( mere-eq-Prop (pair a y) (pair a y'))))
                            ( λ ω v' →
                              apply-universal-property-trunc-Prop
                                ( map-equiv (compute-P ω) v')
                                ( mere-eq-Prop (pair a y) (pair a y'))
                                ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                            ( u)
                            ( v)}
            e : mere-eq {A = Σ A B} (pair a y) (pair a y') ≃
                type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e = equiv-iff
                  ( mere-eq-Prop (pair a y) (pair a y'))
                  ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                  ( λ t →
                    apply-universal-property-trunc-Prop t
                      ( trunc-Prop _)
                      ( ( λ { (pair ω r) →
                            unit-trunc-Prop
                              ( pair
                                ( unit-trunc-Set ω)
                                ( map-inv-equiv
                                  ( compute-P ω)
                                  ( unit-trunc-Prop r)))}) ∘
                        ( pair-eq-Σ)))
                  ( f)
```

### Proposition 1.8

```agda
module _
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : A1 + A2 → B) (e : (A1 + A2) ≃ type-trunc-Set B)
  (H : (unit-trunc-Set ∘ f) ~ map-equiv e)
  where

  map-is-coprod-codomain : (im (f ∘ inl) + im (f ∘ inr)) → B
  map-is-coprod-codomain = ind-coprod (λ x → B) pr1 pr1

  triangle-is-coprod-codomain :
    ( ( map-is-coprod-codomain) ∘
      ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)))) ~ f
  triangle-is-coprod-codomain (inl x) = refl
  triangle-is-coprod-codomain (inr x) = refl

  is-emb-map-is-coprod-codomain : is-emb map-is-coprod-codomain
  is-emb-map-is-coprod-codomain =
    is-emb-coprod
      ( is-emb-inclusion-subtype (λ b → trunc-Prop _))
      ( is-emb-inclusion-subtype (λ b → trunc-Prop _))
      ( λ { (pair b1 u) (pair b2 v) →
          apply-universal-property-trunc-Prop u
            ( function-Prop _ empty-Prop)
            ( λ
              { (pair x refl) →
                apply-universal-property-trunc-Prop v
                  ( function-Prop _ empty-Prop)
                  ( λ
                    { (pair y refl) r →
                      is-empty-eq-coprod-inl-inr x y
                        ( is-injective-is-equiv
                          ( is-equiv-map-equiv e)
                          ( ( inv (H (inl x))) ∙
                            ( ( ap unit-trunc-Set r) ∙
                              ( H (inr y)))))})})})

  is-surjective-map-is-coprod-codomain : is-surjective map-is-coprod-codomain
  is-surjective-map-is-coprod-codomain b =
    apply-universal-property-trunc-Prop
      ( apply-effectiveness-unit-trunc-Set
        ( inv (is-section-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
      ( trunc-Prop (fib map-is-coprod-codomain b))
      ( λ p →
        unit-trunc-Prop
          ( pair
            ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)) a)
            ( triangle-is-coprod-codomain a ∙ inv p)))
    where
    a = map-inv-equiv e (unit-trunc-Set b)

  is-coprod-codomain : (im (f ∘ inl) + im (f ∘ inr)) ≃ B
  pr1 is-coprod-codomain = map-is-coprod-codomain
  pr2 is-coprod-codomain =
    is-equiv-is-emb-is-surjective
      is-surjective-map-is-coprod-codomain
      is-emb-map-is-coprod-codomain

is-0-connected-unit : is-0-connected unit
is-0-connected-unit =
  is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit

is-contr-im :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) {f : A → type-Set B}
  (a : A) (H : f ~ const A (type-Set B) (f a)) → is-contr (im f)
pr1 (is-contr-im B {f} a H) = map-unit-im f a
pr2 (is-contr-im B {f} a H) (pair x u) =
  apply-dependent-universal-property-trunc-Prop
    ( λ v → Id-Prop (im-Set B f) (map-unit-im f a) (pair x v))
    ( u)
    ( λ { (pair a' refl) →
          eq-Eq-im f (map-unit-im f a) (map-unit-im f a') (inv (H a'))})

is-0-connected-im :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-0-connected A → is-0-connected (im f)
is-0-connected-im {l1} {l2} {A} {B} f C =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-0-connected C)
    ( is-contr-Prop _)
    ( λ a →
      is-contr-equiv'
        ( im (map-trunc-Set f))
        ( equiv-trunc-im-Set f)
        ( is-contr-im
          ( trunc-Set B)
          ( unit-trunc-Set a)
          ( apply-dependent-universal-property-trunc-Set'
            ( λ x →
              set-Prop
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f x)
                  ( map-trunc-Set f (unit-trunc-Set a))))
            ( λ a' →
              apply-universal-property-trunc-Prop
                ( mere-eq-is-0-connected C a' a)
                ( Id-Prop
                  ( trunc-Set B)
                  ( map-trunc-Set f (unit-trunc-Set a'))
                  ( map-trunc-Set f (unit-trunc-Set a)))
                ( λ {refl → refl})))))

is-0-connected-im-unit :
  {l1 : Level} {A : UU l1} (f : unit → A) → is-0-connected (im f)
is-0-connected-im-unit f =
  is-0-connected-im f is-0-connected-unit

has-finite-connected-components-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) → (Fin k ≃ (type-trunc-Set A)) →
  ((x y : A) → has-finite-connected-components (Id x y)) →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ' zero-ℕ e H K =
  is-π-finite-is-empty zero-ℕ
    ( is-empty-is-empty-trunc-Set (map-inv-equiv e) ∘ pr1)
has-finite-connected-components-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e H K =
  apply-universal-property-trunc-Prop
    ( has-presentation-of-cardinality-has-cardinality-components
      ( succ-ℕ k)
      ( unit-trunc-Prop e))
    ( has-finite-connected-components-Prop (Σ A B))
    ( α)
  where
  α : Σ (Fin (succ-ℕ k) → A) (λ f → is-equiv (unit-trunc-Set ∘ f)) →
      has-finite-connected-components (Σ A B)
  α (pair f Eηf) =
    is-finite-equiv
      ( equiv-trunc-Set g)
      ( is-finite-equiv'
        ( equiv-distributive-trunc-coprod-Set
          ( Σ (im (f ∘ inl)) (B ∘ pr1))
          ( Σ (im (f ∘ inr)) (B ∘ pr1)))
        ( is-finite-coprod
          ( has-finite-connected-components-Σ' k
            ( h)
            ( λ x y →
              is-finite-equiv'
                ( equiv-trunc-Set
                  ( equiv-ap-emb
                    ( pair pr1
                      ( is-emb-inclusion-subtype
                        ( λ u → trunc-Prop _)))))
                ( H (pr1 x) (pr1 y)))
            ( λ x → K (pr1 x)))
          ( has-finite-connected-components-Σ-is-0-connected
            ( is-0-connected-im (f ∘ inr) is-0-connected-unit)
            ( pair
              ( is-finite-is-contr
                ( is-0-connected-im (f ∘ inr) is-0-connected-unit))
              ( λ x y →
                is-π-finite-equiv zero-ℕ
                  ( equiv-Eq-eq-im (f ∘ inr) x y)
                  ( H (pr1 x) (pr1 y))))
            ( λ x → K (pr1 x)))))
    where
    g : ((Σ (im (f ∘ inl)) (B ∘ pr1)) + (Σ (im (f ∘ inr)) (B ∘ pr1))) ≃
        Σ A B
    g = ( equiv-Σ B
          ( is-coprod-codomain f
            ( pair (unit-trunc-Set ∘ f) Eηf)
            ( refl-htpy))
          ( λ { (inl x) → id-equiv ;
                (inr x) → id-equiv})) ∘e
        ( inv-equiv
          ( right-distributive-Σ-coprod
            ( im (f ∘ inl))
            ( im (f ∘ inr))
            ( ind-coprod (λ x → UU l2) (B ∘ pr1) (B ∘ pr1))))
    i : Fin k → type-trunc-Set (im (f ∘ inl))
    i = unit-trunc-Set ∘ map-unit-im (f ∘ inl)
    is-surjective-i : is-surjective i
    is-surjective-i =
      is-surjective-comp
        ( is-surjective-unit-trunc-Set (im (f ∘ inl)))
        ( is-surjective-map-unit-im (f ∘ inl))
    is-emb-i : is-emb i
    is-emb-i =
      is-emb-right-factor-htpy
        ( (unit-trunc-Set ∘ f) ∘ inl)
        ( inclusion-trunc-im-Set (f ∘ inl))
        ( i)
        ( ( inv-htpy (naturality-unit-trunc-Set (inclusion-im (f ∘ inl)))) ·r
          ( map-unit-im (f ∘ inl)))
        ( is-emb-inclusion-trunc-im-Set (f ∘ inl))
        ( is-emb-comp
          ( unit-trunc-Set ∘ f)
          ( inl)
          ( is-emb-is-equiv Eηf)
          ( is-emb-inl (Fin k) unit))
    h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
    h = pair i (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)

has-finite-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-π-finite 1 A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ {l1} {l2} {A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finite-connected-components-Prop (Σ A B))
    ( λ { (pair k e) →
          has-finite-connected-components-Σ' k e (λ x y → pr2 H x y) K})

is-π-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-π-finite (succ-ℕ k) A → ((x : A) → is-π-finite k (B x)) →
  is-π-finite k (Σ A B)
is-π-finite-Σ zero-ℕ {A} {B} H K = has-finite-connected-components-Σ H K
pr1 (is-π-finite-Σ (succ-ℕ k) H K) =
  has-finite-connected-components-Σ
    ( is-π-finite-one-is-π-finite-succ-ℕ (succ-ℕ k) H)
    ( λ x →
      has-finite-connected-components-is-π-finite (succ-ℕ k) (K x))
pr2 (is-π-finite-Σ (succ-ℕ k) H K) (pair x u) (pair y v) =
  is-π-finite-equiv k
    ( equiv-pair-eq-Σ (pair x u) (pair y v))
    ( is-π-finite-Σ k
      ( pr2 H x y)
      ( λ { refl → pr2 (K x) u v}))

π-Finite-Σ :
  {l1 l2 : Level} (k : ℕ) (A : π-Finite l1 (succ-ℕ k))
  (B : (x : type-π-Finite (succ-ℕ k) A) → π-Finite l2 k) →
  π-Finite (l1 ⊔ l2) k
pr1 (π-Finite-Σ k A B) =
  Σ (type-π-Finite (succ-ℕ k) A) (λ x → type-π-Finite k (B x))
pr2 (π-Finite-Σ k A B) =
  is-π-finite-Σ k
    ( is-π-finite-type-π-Finite (succ-ℕ k) A)
    ( λ x → is-π-finite-type-π-Finite k (B x))
```
