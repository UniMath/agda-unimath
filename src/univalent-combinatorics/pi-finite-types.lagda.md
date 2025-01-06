# Untruncated π-finite types

```agda
module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-identifications
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equality
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is
{{#concept "untruncated πₙ-finite" Disambiguation="type" Agda=is-untruncated-π-finite Agda=Untruncated-π-Finite-Type}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md) and all of its
homotopy groups up to level `n` at all base points are finite.

## Definitions

### Untruncated π-finite types

```agda
is-untruncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-untruncated-π-finite-Prop zero-ℕ X =
  has-finitely-many-connected-components-Prop X
is-untruncated-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( is-untruncated-π-finite-Prop zero-ℕ X)
    ( Π-Prop X (λ x → Π-Prop X (λ y → is-untruncated-π-finite-Prop k (x ＝ y))))

is-untruncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-untruncated-π-finite k X = type-Prop (is-untruncated-π-finite-Prop k X)

is-prop-is-untruncated-π-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-untruncated-π-finite k X)
is-prop-is-untruncated-π-finite k X =
  is-prop-type-Prop (is-untruncated-π-finite-Prop k X)

Untruncated-π-Finite-Type : (l : Level) (k : ℕ) → UU (lsuc l)
Untruncated-π-Finite-Type l k = Σ (UU l) (is-untruncated-π-finite k)

type-Untruncated-π-Finite-Type :
  {l : Level} (k : ℕ) → Untruncated-π-Finite-Type l k → UU l
type-Untruncated-π-Finite-Type k = pr1

is-untruncated-π-finite-type-Untruncated-π-Finite-Type :
  {l : Level} (k : ℕ) (A : Untruncated-π-Finite-Type l k) →
  is-untruncated-π-finite k (type-Untruncated-π-Finite-Type {l} k A)
is-untruncated-π-finite-type-Untruncated-π-Finite-Type k = pr2

has-finitely-many-connected-components-is-untruncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-untruncated-π-finite k A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-untruncated-π-finite zero-ℕ H = H
has-finitely-many-connected-components-is-untruncated-π-finite (succ-ℕ k) H =
  pr1 H
```

## Properties

### Untruncated π-finite types are closed under equivalences

```agda
is-untruncated-π-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-untruncated-π-finite k B → is-untruncated-π-finite k A
is-untruncated-π-finite-equiv zero-ℕ =
  has-finitely-many-connected-components-equiv'
pr1 (is-untruncated-π-finite-equiv (succ-ℕ k) e H) =
  is-untruncated-π-finite-equiv zero-ℕ e (pr1 H)
pr2 (is-untruncated-π-finite-equiv (succ-ℕ k) e H) a b =
  is-untruncated-π-finite-equiv k
    ( equiv-ap e a b)
    ( pr2 H (map-equiv e a) (map-equiv e b))

is-untruncated-π-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-untruncated-π-finite k A → is-untruncated-π-finite k B
is-untruncated-π-finite-equiv' k e =
  is-untruncated-π-finite-equiv k (inv-equiv e)
```

### Untruncated π-finite types are closed under retracts

```agda
is-untruncated-π-finite-retract :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A retract-of B → is-untruncated-π-finite k B → is-untruncated-π-finite k A
is-untruncated-π-finite-retract zero-ℕ =
  has-finitely-many-connected-components-retract
pr1 (is-untruncated-π-finite-retract (succ-ℕ k) r H) =
  is-untruncated-π-finite-retract zero-ℕ r
    ( has-finitely-many-connected-components-is-untruncated-π-finite
      ( succ-ℕ k)
      ( H))
pr2 (is-untruncated-π-finite-retract (succ-ℕ k) r H) x y =
  is-untruncated-π-finite-retract k
    ( retract-eq r x y)
    ( pr2 H (inclusion-retract r x) (inclusion-retract r y))
```

### Empty types are untruncated π-finite

```agda
is-untruncated-π-finite-empty : (k : ℕ) → is-untruncated-π-finite k empty
is-untruncated-π-finite-empty zero-ℕ =
  has-finitely-many-connected-components-empty
pr1 (is-untruncated-π-finite-empty (succ-ℕ k)) =
  is-untruncated-π-finite-empty zero-ℕ
pr2 (is-untruncated-π-finite-empty (succ-ℕ k)) = ind-empty

empty-Untruncated-π-Finite-Type : (k : ℕ) → Untruncated-π-Finite-Type lzero k
pr1 (empty-Untruncated-π-Finite-Type k) = empty
pr2 (empty-Untruncated-π-Finite-Type k) = is-untruncated-π-finite-empty k

is-untruncated-π-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-empty zero-ℕ =
  has-finitely-many-connected-components-is-empty
pr1 (is-untruncated-π-finite-is-empty (succ-ℕ k) f) =
  is-untruncated-π-finite-is-empty zero-ℕ f
pr2 (is-untruncated-π-finite-is-empty (succ-ℕ k) f) a = ex-falso (f a)
```

### Contractible types are untruncated π-finite

```agda
is-untruncated-π-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-contr zero-ℕ =
  has-finitely-many-connected-components-is-contr
pr1 (is-untruncated-π-finite-is-contr (succ-ℕ k) H) =
  is-untruncated-π-finite-is-contr zero-ℕ H
pr2 (is-untruncated-π-finite-is-contr (succ-ℕ k) H) x y =
  is-untruncated-π-finite-is-contr k ( is-prop-is-contr H x y)

is-untruncated-π-finite-unit : (k : ℕ) → is-untruncated-π-finite k unit
is-untruncated-π-finite-unit k =
  is-untruncated-π-finite-is-contr k is-contr-unit

unit-Untruncated-π-Finite-Type : (k : ℕ) → Untruncated-π-Finite-Type lzero k
pr1 (unit-Untruncated-π-Finite-Type k) = unit
pr2 (unit-Untruncated-π-Finite-Type k) = is-untruncated-π-finite-unit k
```

### Coproducts of untruncated π-finite types are untruncated π-finite

```agda
is-untruncated-π-finite-coproduct :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-untruncated-π-finite k A → is-untruncated-π-finite k B →
  is-untruncated-π-finite k (A + B)
is-untruncated-π-finite-coproduct zero-ℕ =
  has-finitely-many-connected-components-coproduct
pr1 (is-untruncated-π-finite-coproduct (succ-ℕ k) H K) =
  is-untruncated-π-finite-coproduct zero-ℕ (pr1 H) (pr1 K)
pr2 (is-untruncated-π-finite-coproduct (succ-ℕ k) H K) (inl x) (inl y) =
  is-untruncated-π-finite-equiv k
    ( compute-eq-coproduct-inl-inl x y)
    ( pr2 H x y)
pr2 (is-untruncated-π-finite-coproduct (succ-ℕ k) H K) (inl x) (inr y) =
  is-untruncated-π-finite-equiv k
    ( compute-eq-coproduct-inl-inr x y)
    ( is-untruncated-π-finite-empty k)
pr2 (is-untruncated-π-finite-coproduct (succ-ℕ k) H K) (inr x) (inl y) =
  is-untruncated-π-finite-equiv k
    ( compute-eq-coproduct-inr-inl x y)
    ( is-untruncated-π-finite-empty k)
pr2 (is-untruncated-π-finite-coproduct (succ-ℕ k) H K) (inr x) (inr y) =
  is-untruncated-π-finite-equiv k
    ( compute-eq-coproduct-inr-inr x y)
    ( pr2 K x y)

coproduct-Untruncated-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) →
  Untruncated-π-Finite-Type l1 k →
  Untruncated-π-Finite-Type l2 k →
  Untruncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (coproduct-Untruncated-π-Finite-Type k A B) =
  (type-Untruncated-π-Finite-Type k A + type-Untruncated-π-Finite-Type k B)
pr2 (coproduct-Untruncated-π-Finite-Type k A B) =
  is-untruncated-π-finite-coproduct k
    ( is-untruncated-π-finite-type-Untruncated-π-Finite-Type k A)
    ( is-untruncated-π-finite-type-Untruncated-π-Finite-Type k B)
```

### `Maybe A` of any untruncated π-finite type `A` is untruncated π-finite

```agda
Maybe-Untruncated-π-Finite-Type :
  {l : Level} (k : ℕ) →
  Untruncated-π-Finite-Type l k →
  Untruncated-π-Finite-Type l k
Maybe-Untruncated-π-Finite-Type k A =
  coproduct-Untruncated-π-Finite-Type k A (unit-Untruncated-π-Finite-Type k)

is-untruncated-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-untruncated-π-finite k A → is-untruncated-π-finite k (Maybe A)
is-untruncated-π-finite-Maybe k H =
  is-untruncated-π-finite-coproduct k H (is-untruncated-π-finite-unit k)
```

### Any stanadard finite type is untruncated π-finite

```agda
is-untruncated-π-finite-Fin :
  (k n : ℕ) → is-untruncated-π-finite k (Fin n)
is-untruncated-π-finite-Fin k zero-ℕ =
  is-untruncated-π-finite-empty k
is-untruncated-π-finite-Fin k (succ-ℕ n) =
  is-untruncated-π-finite-Maybe k (is-untruncated-π-finite-Fin k n)

Fin-Untruncated-π-Finite-Type :
  (k : ℕ) (n : ℕ) → Untruncated-π-Finite-Type lzero k
pr1 (Fin-Untruncated-π-Finite-Type k n) = Fin n
pr2 (Fin-Untruncated-π-Finite-Type k n) = is-untruncated-π-finite-Fin k n
```

### Any type equipped with a counting is untruncated π-finite

```agda
is-untruncated-π-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-untruncated-π-finite k A
is-untruncated-π-finite-count k (n , e) =
  is-untruncated-π-finite-equiv' k e (is-untruncated-π-finite-Fin k n)
```

### Any finite type is untruncated π-finite

```agda
is-untruncated-π-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-untruncated-π-finite-Prop k A)
    ( is-untruncated-π-finite-count k)

π-finite-𝔽 : {l : Level} (k : ℕ) → 𝔽 l → Untruncated-π-Finite-Type l k
pr1 (π-finite-𝔽 k A) = type-𝔽 A
pr2 (π-finite-𝔽 k A) = is-untruncated-π-finite-is-finite k (is-finite-type-𝔽 A)
```

### The type of all `n`-element types in `UU l` is untruncated π-finite

```agda
is-untruncated-π-finite-UU-Fin :
  {l : Level} (k n : ℕ) → is-untruncated-π-finite k (UU-Fin l n)
is-untruncated-π-finite-UU-Fin zero-ℕ n =
  has-finitely-many-connected-components-UU-Fin n
pr1 (is-untruncated-π-finite-UU-Fin (succ-ℕ k) n) =
  is-untruncated-π-finite-UU-Fin zero-ℕ n
pr2 (is-untruncated-π-finite-UU-Fin (succ-ℕ k) n) x y =
  is-untruncated-π-finite-equiv k
    ( equiv-equiv-eq-UU-Fin n x y)
    ( is-untruncated-π-finite-is-finite k
      ( is-finite-≃
        ( is-finite-has-finite-cardinality (n , pr2 x))
        ( is-finite-has-finite-cardinality (n , pr2 y))))
```

### Untruncated πₙ₊₁-finite types are untruncated πₙ-finite

```agda
is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-untruncated-π-finite (succ-ℕ k) A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ zero-ℕ H =
  has-finitely-many-connected-components-is-untruncated-π-finite 1 H
pr1 (is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ (succ-ℕ k) H) =
  has-finitely-many-connected-components-is-untruncated-π-finite
    ( succ-ℕ (succ-ℕ k))
    ( H)
pr2 (is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ (succ-ℕ k) H) x y =
  is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ k (pr2 H x y)
```

### Untruncated πₙ₊₁-finite types are untruncated π₁-finite

```agda
is-untruncated-π-finite-one-is-untruncated-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-untruncated-π-finite (succ-ℕ k) A → is-untruncated-π-finite 1 A
is-untruncated-π-finite-one-is-untruncated-π-finite-succ-ℕ zero-ℕ H = H
is-untruncated-π-finite-one-is-untruncated-π-finite-succ-ℕ (succ-ℕ k) H =
  is-untruncated-π-finite-one-is-untruncated-π-finite-succ-ℕ k
    ( is-untruncated-π-finite-is-untruncated-π-finite-succ-ℕ (succ-ℕ k) H)
```

### Untruncated πₙ-finite sets are finite

```agda
is-finite-is-untruncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-untruncated-π-finite k A → is-finite A
is-finite-is-untruncated-π-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-untruncated-π-finite k K)
```

### Finite products of untruncated π-finite types are untruncated π-finite

```agda
is-untruncated-π-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-untruncated-π-finite k (B a)) →
  is-untruncated-π-finite k ((a : A) → B a)
is-untruncated-π-finite-Π zero-ℕ =
  has-finitely-many-connected-components-finite-Π
pr1 (is-untruncated-π-finite-Π (succ-ℕ k) H K) =
  is-untruncated-π-finite-Π zero-ℕ H (λ a → pr1 (K a))
pr2 (is-untruncated-π-finite-Π (succ-ℕ k) H K) f g =
  is-untruncated-π-finite-equiv k
    ( equiv-funext)
    ( is-untruncated-π-finite-Π k H (λ a → pr2 (K a) (f a) (g a)))

Untruncated-π-Finite-Type-Π :
  {l1 l2 : Level} (k : ℕ) (A : 𝔽 l1)
  (B : type-𝔽 A → Untruncated-π-Finite-Type l2 k) →
  Untruncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (Untruncated-π-Finite-Type-Π k A B) =
  (x : type-𝔽 A) → (type-Untruncated-π-Finite-Type k (B x))
pr2 (Untruncated-π-Finite-Type-Π k A B) =
  is-untruncated-π-finite-Π k
    ( is-finite-type-𝔽 A)
    ( λ x → is-untruncated-π-finite-type-Untruncated-π-Finite-Type k (B x))
```

### Dependent sums of types with finitely many connected components over a `0`-connected base

The total space of a family of types with finitely many connected components
over a `0`-connected base has finitely many connected components when the based
[loop spaces](synthetic-homotopy-theory.loop-spaces.md) of the base have
finitely many connected components.

```agda
has-finitely-many-connected-components-Σ-is-0-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-0-connected A →
  ((a : A) → has-finitely-many-connected-components (a ＝ a)) →
  ((x : A) → has-finitely-many-connected-components (B x)) →
  has-finitely-many-connected-components (Σ A B)
has-finitely-many-connected-components-Σ-is-0-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-0-connected C)
    ( has-finitely-many-connected-components-Prop (Σ A B))
    ( α)
  where
  α : A → has-finitely-many-connected-components (Σ A B)
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
    β :
      (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
      is-decidable (unit-trunc-Set x ＝ v)
    β (x , y) =
      apply-dependent-universal-property-trunc-Set'
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (x , y)) u)))
        ( γ)
      where
      γ :
        (v : Σ A B) →
        is-decidable ((unit-trunc-Set (x , y)) ＝ (unit-trunc-Set v))
      γ (x' , y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( x , y)
            ( x' , y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (x , y) (x' , y')))
              ( δ))
        where
        δ : a ＝ x → is-decidable (mere-eq (x , y) (x' , y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (a , y) (x' , y')))
            ( ε)
          where
          ε : a ＝ x' → is-decidable (mere-eq (x , y) (x' , y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( H a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))
            where
            ℙ :
              is-contr
                ( Σ ( hom-Set (trunc-Set (a ＝ a)) (Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ →
                        trunc-Prop (dependent-identification B ω₁ y y'))))
            ℙ =
              universal-property-trunc-Set
                ( a ＝ a)
                ( Prop-Set _)
                ( λ ω → trunc-Prop (dependent-identification B ω y y'))

            P : type-trunc-Set (Id a a) → Prop _
            P = pr1 (center ℙ)

            compute-P :
              (ω : a ＝ a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (dependent-identification B ω y y')
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))

            d : (t : type-trunc-Set (a ＝ a)) → is-decidable (type-Prop (P t))
            d =
              apply-dependent-universal-property-trunc-Set'
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
                ( mere-eq-Prop {A = Σ A B} (a , y) (a , y'))
            f t =
              apply-universal-property-trunc-Prop t
                ( mere-eq-Prop (a , y) (a , y'))
                  λ (u , v) →
                  apply-dependent-universal-property-trunc-Set'
                    ( λ u' →
                      hom-set-Set
                        ( set-Prop (P u'))
                        ( set-Prop
                          ( mere-eq-Prop (a , y) (a , y'))))
                    ( λ ω v' →
                      apply-universal-property-trunc-Prop
                        ( map-equiv (compute-P ω) v')
                        ( mere-eq-Prop (a , y) (a , y'))
                        ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                    ( u)
                    ( v)
            e :
              mere-eq {A = Σ A B} (a , y) (a , y') ≃
              type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e =
              equiv-iff
                ( mere-eq-Prop (a , y) (a , y'))
                ( trunc-Prop (Σ (type-trunc-Set (a ＝ a)) (type-Prop ∘ P)))
                ( λ t →
                  apply-universal-property-trunc-Prop t
                    ( trunc-Prop _)
                    ( ( λ (ω , r) →
                        unit-trunc-Prop
                          { A = Σ (type-trunc-Set (a ＝ a)) (type-Prop ∘ P)}
                          ( ( unit-trunc-Set ω) ,
                            ( map-inv-equiv
                              ( compute-P ω)
                              ( unit-trunc-Prop r)))) ∘
                      ( pair-eq-Σ)))
                ( f)
```

### Dependent sums of types with finitely many connected components

```agda
abstract
  has-finitely-many-connected-components-Σ' :
    {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
    (Fin k ≃ type-trunc-Set A) →
    ((x y : A) → has-finitely-many-connected-components (x ＝ y)) →
    ((x : A) → has-finitely-many-connected-components (B x)) →
    has-finitely-many-connected-components (Σ A B)
  has-finitely-many-connected-components-Σ' zero-ℕ e H K =
    has-finitely-many-connected-components-is-empty
      ( is-empty-is-empty-trunc-Set (map-inv-equiv e) ∘ pr1)
  has-finitely-many-connected-components-Σ' (succ-ℕ k) {A} {B} e H K =
    apply-universal-property-trunc-Prop
      ( has-presentation-of-cardinality-has-cardinality-connected-components
        ( succ-ℕ k)
        ( unit-trunc-Prop e))
      ( has-finitely-many-connected-components-Prop (Σ A B))
      ( α)
    where
    α : Σ (Fin (succ-ℕ k) → A) (λ f → is-equiv (unit-trunc-Set ∘ f)) →
        has-finitely-many-connected-components (Σ A B)
    α (f , Eηf) =
      is-finite-equiv
        ( equiv-trunc-Set g)
        ( is-finite-equiv'
          ( equiv-distributive-trunc-coproduct-Set
            ( Σ (im (f ∘ inl)) (B ∘ pr1))
            ( Σ (im (f ∘ inr)) (B ∘ pr1)))
          ( is-finite-coproduct
            ( has-finitely-many-connected-components-Σ' k
              ( h)
              ( λ x y →
                is-finite-equiv'
                  ( equiv-trunc-Set
                    ( equiv-ap-emb
                      ( pr1 , is-emb-inclusion-subtype ( λ u → trunc-Prop _))))
                  ( H (pr1 x) (pr1 y)))
              ( λ x → K (pr1 x)))
            ( has-finitely-many-connected-components-Σ-is-0-connected
              ( is-0-connected-im-is-0-connected-domain
                ( f ∘ inr)
                ( is-0-connected-unit))
              ( λ a →
                has-finitely-many-connected-components-equiv'
                  ( equiv-Eq-eq-im (f ∘ inr) a a)
                  ( H (pr1 a) (pr1 a)))
              ( λ x → K (pr1 x)))))
      where
      g : ((Σ (im (f ∘ inl)) (B ∘ pr1)) + (Σ (im (f ∘ inr)) (B ∘ pr1))) ≃
          Σ A B
      g =
        ( equiv-Σ B
          ( is-coproduct-codomain f
            ( unit-trunc-Set ∘ f , Eηf)
            ( refl-htpy))
          ( λ { (inl x) → id-equiv ; (inr x) → id-equiv})) ∘e
        ( inv-equiv
          ( right-distributive-Σ-coproduct
            ( im (f ∘ inl))
            ( im (f ∘ inr))
            ( rec-coproduct (B ∘ pr1) (B ∘ pr1))))

      i : Fin k → type-trunc-Set (im (f ∘ inl))
      i = unit-trunc-Set ∘ map-unit-im (f ∘ inl)

      is-surjective-i : is-surjective i
      is-surjective-i =
        is-surjective-comp
          ( is-surjective-unit-trunc-Set (im (f ∘ inl)))
          ( is-surjective-map-unit-im (f ∘ inl))

      is-emb-i : is-emb i
      is-emb-i =
        is-emb-top-map-triangle
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
            ( is-emb-inl))
      h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
      h = i , (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)
```

### Dependent sums of untruncated π-finite types

The dependent sum of a family of untruncated πₙ-finite types over a untruncated
πₙ₊₁-finite base is untruncated πₙ-finite.

```agda
has-finitely-many-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-untruncated-π-finite 1 A →
  ((x : A) → has-finitely-many-connected-components (B x)) →
  has-finitely-many-connected-components (Σ A B)
has-finitely-many-connected-components-Σ {A = A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finitely-many-connected-components-Prop (Σ A B))
    ( λ (k , e) →
      has-finitely-many-connected-components-Σ' k e (λ x y → pr2 H x y) K)

abstract
  is-untruncated-π-finite-Σ :
    {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
    is-untruncated-π-finite (succ-ℕ k) A →
    ((x : A) → is-untruncated-π-finite k (B x)) →
    is-untruncated-π-finite k (Σ A B)
  is-untruncated-π-finite-Σ zero-ℕ =
    has-finitely-many-connected-components-Σ
  pr1 (is-untruncated-π-finite-Σ (succ-ℕ k) H K) =
    has-finitely-many-connected-components-Σ
      ( is-untruncated-π-finite-one-is-untruncated-π-finite-succ-ℕ (succ-ℕ k) H)
      ( λ x →
        has-finitely-many-connected-components-is-untruncated-π-finite
          ( succ-ℕ k)
          ( K x))
  pr2 (is-untruncated-π-finite-Σ (succ-ℕ k) H K) (x , u) (y , v) =
    is-untruncated-π-finite-equiv k
      ( equiv-pair-eq-Σ (x , u) (y , v))
      ( is-untruncated-π-finite-Σ k
        ( pr2 H x y)
        ( λ where refl → pr2 (K x) u v))

Untruncated-π-Finite-Type-Σ :
  {l1 l2 : Level} (k : ℕ) (A : Untruncated-π-Finite-Type l1 (succ-ℕ k))
  (B :
    (x : type-Untruncated-π-Finite-Type (succ-ℕ k) A) →
    Untruncated-π-Finite-Type l2 k) →
  Untruncated-π-Finite-Type (l1 ⊔ l2) k
pr1 (Untruncated-π-Finite-Type-Σ k A B) =
  Σ ( type-Untruncated-π-Finite-Type (succ-ℕ k) A)
    ( λ x → type-Untruncated-π-Finite-Type k (B x))
pr2 (Untruncated-π-Finite-Type-Σ k A B) =
  is-untruncated-π-finite-Σ k
    ( is-untruncated-π-finite-type-Untruncated-π-Finite-Type (succ-ℕ k) A)
    ( λ x → is-untruncated-π-finite-type-Untruncated-π-Finite-Type k (B x))
```

## See also

- [π-finite types](univalent-combinatorics.truncated-pi-finite-types.md)
- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)
