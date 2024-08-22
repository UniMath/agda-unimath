# π-finite types

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
open import foundation.dependent-pair-types
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
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
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
{{#concept "`πₙ`-finite" Disambiguation="type" Agda=is-π-finite Agda=π-Finite}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md) and all of its
homotopy groups up to level `n` at all base points are finite.

## Definition

### Truncated π-finite types

```agda
is-truncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-truncated-π-finite-Prop zero-ℕ X = is-finite-Prop X
is-truncated-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( has-finitely-many-connected-components-Prop X)
    ( Π-Prop X
      ( λ x → Π-Prop X (λ y → is-truncated-π-finite-Prop k (x ＝ y))))

is-truncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-truncated-π-finite k A =
  type-Prop (is-truncated-π-finite-Prop k A)
```

### π-finite types

```agda
is-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-π-finite-Prop zero-ℕ X = has-finitely-many-connected-components-Prop X
is-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( is-π-finite-Prop zero-ℕ X)
    ( Π-Prop X (λ x → Π-Prop X (λ y → is-π-finite-Prop k (x ＝ y))))

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

has-finitely-many-connected-components-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-π-finite zero-ℕ H = H
has-finitely-many-connected-components-is-π-finite (succ-ℕ k) H = pr1 H
```

## Properties

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
is-π-finite-unit : (k : ℕ) → is-π-finite k unit
is-π-finite-unit k = is-π-finite-is-contr k is-contr-unit

unit-π-Finite : (k : ℕ) → π-Finite lzero k
pr1 (unit-π-Finite k) = unit
pr2 (unit-π-Finite k) = is-π-finite-unit k
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coproduct :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-π-finite k A → is-π-finite k B →
  is-π-finite k (A + B)
is-π-finite-coproduct zero-ℕ H K =
  is-finite-equiv'
    ( equiv-distributive-trunc-coproduct-Set _ _)
    ( is-finite-coproduct H K)
pr1 (is-π-finite-coproduct (succ-ℕ k) H K) =
  is-π-finite-coproduct zero-ℕ (pr1 H) (pr1 K)
pr2 (is-π-finite-coproduct (succ-ℕ k) H K) (inl x) (inl y) =
  is-π-finite-equiv k
    ( compute-eq-coproduct-inl-inl x y)
    ( pr2 H x y)
pr2 (is-π-finite-coproduct (succ-ℕ k) H K) (inl x) (inr y) =
  is-π-finite-equiv k
    ( compute-eq-coproduct-inl-inr x y)
    ( is-π-finite-empty k)
pr2 (is-π-finite-coproduct (succ-ℕ k) H K) (inr x) (inl y) =
  is-π-finite-equiv k
    ( compute-eq-coproduct-inr-inl x y)
    ( is-π-finite-empty k)
pr2 (is-π-finite-coproduct (succ-ℕ k) H K) (inr x) (inr y) =
  is-π-finite-equiv k
    ( compute-eq-coproduct-inr-inr x y)
    ( pr2 K x y)

coproduct-π-Finite :
  {l1 l2 : Level} (k : ℕ) →
  π-Finite l1 k → π-Finite l2 k → π-Finite (l1 ⊔ l2) k
pr1 (coproduct-π-Finite k A B) =
  (type-π-Finite k A + type-π-Finite k B)
pr2 (coproduct-π-Finite k A B) =
  is-π-finite-coproduct k
    ( is-π-finite-type-π-Finite k A)
    ( is-π-finite-type-π-Finite k B)
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
Maybe-π-Finite :
  {l : Level} (k : ℕ) → π-Finite l k → π-Finite l k
Maybe-π-Finite k A =
  coproduct-π-Finite k A (unit-π-Finite k)

is-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → is-π-finite k (Maybe A)
is-π-finite-Maybe k H =
  is-π-finite-coproduct k H (is-π-finite-unit k)
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
is-π-finite-count k (n , e) =
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

### The type of all `n`-element types in `UU l` is π-finite

```agda
is-π-finite-UU-Fin :
  {l : Level} (k n : ℕ) → is-π-finite k (UU-Fin l n)
is-π-finite-UU-Fin zero-ℕ n =
  has-finitely-many-connected-components-is-0-connected
    ( is-0-connected-UU-Fin n)
pr1 (is-π-finite-UU-Fin (succ-ℕ k) n) =
  is-π-finite-UU-Fin zero-ℕ n
pr2 (is-π-finite-UU-Fin (succ-ℕ k) n) x y =
  is-π-finite-equiv k
    ( equiv-equiv-eq-UU-Fin n x y)
    ( is-π-finite-is-finite k
      ( is-finite-≃
        ( is-finite-has-finite-cardinality (n , (pr2 x)))
        ( is-finite-has-finite-cardinality (n , (pr2 y)))))
```

### πₙ₊₁-finite types are πₙ-finite

```agda
is-π-finite-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite k A
is-π-finite-is-π-finite-succ-ℕ zero-ℕ H =
  has-finitely-many-connected-components-is-π-finite 1 H
pr1 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) =
  has-finitely-many-connected-components-is-π-finite (succ-ℕ (succ-ℕ k)) H
pr2 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) x y =
  is-π-finite-is-π-finite-succ-ℕ k (pr2 H x y)
```

### πₙ₊₁-finite types are π₁-finite

```agda
is-π-finite-one-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite 1 A
is-π-finite-one-is-π-finite-succ-ℕ zero-ℕ H = H
is-π-finite-one-is-π-finite-succ-ℕ (succ-ℕ k) H =
  is-π-finite-one-is-π-finite-succ-ℕ k
    ( is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H)
```

### πₙ-finite sets are finite

```agda
is-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-π-finite k A → is-finite A
is-finite-is-π-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-π-finite k K)
```

### πₙ-finite n-truncated types are truncated πₙ-finite

```agda
is-truncated-π-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-π-finite zero-ℕ H K =
  is-finite-is-π-finite zero-ℕ H K
pr1 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) x y =
  is-truncated-π-finite-is-π-finite k (H x y) (pr2 K x y)
```

### truncated πₙ-finite types are πₙ-finite

```agda
is-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-π-finite k A
is-π-finite-is-truncated-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (_ , (is-set-is-finite H)))
    ( H)
pr1 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) = pr1 H
pr2 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y =
  is-π-finite-is-truncated-π-finite k (pr2 H x y)
```

### Finite products of π-finite types are π-finite

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
              ( ( λ a →
                  has-finitely-many-connected-components-equiv'
                    ( equiv-Eq-eq-im (f ∘ inr) a a)
                    ( H (pr1 a) (pr1 a))))
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
            ( is-emb-inl (Fin k) unit))

      h : Fin k ≃ type-trunc-Set (im (f ∘ inl))
      h = i , (is-equiv-is-emb-is-surjective is-surjective-i is-emb-i)
```

### Dependent sums of π-finite types

The dependent sum of a family of πₙ-finite types over a πₙ₊₁-finite base is
πₙ-finite.

```agda
has-finitely-many-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-π-finite 1 A →
  ((x : A) → has-finitely-many-connected-components (B x)) →
  has-finitely-many-connected-components (Σ A B)
has-finitely-many-connected-components-Σ {A = A} {B} H K =
  apply-universal-property-trunc-Prop
    ( pr1 H)
    ( has-finitely-many-connected-components-Prop (Σ A B))
    ( λ (k , e) →
      has-finitely-many-connected-components-Σ' k e (λ x y → pr2 H x y) K)

abstract
  is-π-finite-Σ :
    {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
    is-π-finite (succ-ℕ k) A → ((x : A) → is-π-finite k (B x)) →
    is-π-finite k (Σ A B)
  is-π-finite-Σ zero-ℕ =
    has-finitely-many-connected-components-Σ
  pr1 (is-π-finite-Σ (succ-ℕ k) H K) =
    has-finitely-many-connected-components-Σ
      ( is-π-finite-one-is-π-finite-succ-ℕ (succ-ℕ k) H)
      ( λ x →
        has-finitely-many-connected-components-is-π-finite (succ-ℕ k) (K x))
  pr2 (is-π-finite-Σ (succ-ℕ k) H K) (x , u) (y , v) =
    is-π-finite-equiv k
      ( equiv-pair-eq-Σ (x , u) (y , v))
      ( is-π-finite-Σ k
        ( pr2 H x y)
        ( λ where refl → pr2 (K x) u v))

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

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
