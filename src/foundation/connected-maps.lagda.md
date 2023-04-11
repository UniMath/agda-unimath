# Connected maps

<details><summary>Imports</summary>
```agda
module foundation.connected-maps where
open import elementary-number-theory.natural-numbers
open import foundation.connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
```
</details>

## Idea

A map is said to be **`k`-connected** if its fibers are `k`-connected types.

## Definitions

### Connected maps

```agda
is-connected-map-Prop :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-connected-map-Prop k {B = B} f =
  Π-Prop B (λ b → is-connected-Prop k (fib f b))

is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-connected-map k f = type-Prop (is-connected-map-Prop k f)

is-prop-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-connected-map k f)
is-prop-is-connected-map k f = is-prop-type-Prop (is-connected-map-Prop k f)
```

### The type of connected maps between two types

```agda
connected-map : {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
connected-map k A B = type-subtype (is-connected-map-Prop k {A} {B})

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-connected-map : connected-map k A B → A → B
  map-connected-map = inclusion-subtype (is-connected-map-Prop k)

  is-connected-map-connected-map :
    (f : connected-map k A B) → is-connected-map k (map-connected-map f)
  is-connected-map-connected-map =
    is-in-subtype-inclusion-subtype (is-connected-map-Prop k)

  emb-inclusion-connected-map : connected-map k A B ↪ (A → B)
  emb-inclusion-connected-map = emb-subtype (is-connected-map-Prop k)

  htpy-connected-map : (f g : connected-map k A B) → UU (l1 ⊔ l2)
  htpy-connected-map f g = (map-connected-map f) ~ (map-connected-map g)

  refl-htpy-connected-map : (f : connected-map k A B) → htpy-connected-map f f
  refl-htpy-connected-map f = refl-htpy

  is-contr-total-htpy-connected-map :
    (f : connected-map k A B) →
    is-contr (Σ (connected-map k A B) (htpy-connected-map f))
  is-contr-total-htpy-connected-map f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-connected-map f))
      ( is-prop-is-connected-map k)
      ( map-connected-map f)
      ( refl-htpy-connected-map f)
      ( is-connected-map-connected-map f)

  htpy-eq-connected-map :
    (f g : connected-map k A B) → f ＝ g → htpy-connected-map f g
  htpy-eq-connected-map f .f refl = refl-htpy-connected-map f

  is-equiv-htpy-eq-connected-map :
    (f g : connected-map k A B) → is-equiv (htpy-eq-connected-map f g)
  is-equiv-htpy-eq-connected-map f =
    fundamental-theorem-id
      ( is-contr-total-htpy-connected-map f)
      ( htpy-eq-connected-map f)

  extensionality-connected-map :
    (f g : connected-map k A B) → (f ＝ g) ≃ htpy-connected-map f g
  pr1 (extensionality-connected-map f g) = htpy-eq-connected-map f g
  pr2 (extensionality-connected-map f g) = is-equiv-htpy-eq-connected-map f g

  eq-htpy-connected-map :
    (f g : connected-map k A B) → htpy-connected-map f g → (f ＝ g)
  eq-htpy-connected-map f g =
    map-inv-equiv (extensionality-connected-map f g)
```

### The type of connected maps into a type

```agda
Connected-Map :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map l2 k A = Σ (UU l2) (λ X → connected-map k A X)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  type-Connected-Map : UU l2
  type-Connected-Map = pr1 f

  connected-map-Connected-Map : connected-map k A type-Connected-Map
  connected-map-Connected-Map = pr2 f

  map-Connected-Map : A → type-Connected-Map
  map-Connected-Map = map-connected-map connected-map-Connected-Map

  is-connected-map-Connected-Map : is-connected-map k map-Connected-Map
  is-connected-map-Connected-Map =
    is-connected-map-connected-map connected-map-Connected-Map
```

### The type of connected maps into a truncated type

```agda
Connected-Map-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k l : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map-Into-Truncated-Type l2 k l A =
  Σ (Truncated-Type l2 l) (λ X → connected-map k A (type-Truncated-Type X))

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  truncated-type-Connected-Map-Into-Truncated-Type : Truncated-Type l2 l
  truncated-type-Connected-Map-Into-Truncated-Type = pr1 f

  type-Connected-Map-Into-Truncated-Type : UU l2
  type-Connected-Map-Into-Truncated-Type =
    type-Truncated-Type truncated-type-Connected-Map-Into-Truncated-Type

  is-trunc-type-Connected-Map-Into-Truncated-Type :
    is-trunc l type-Connected-Map-Into-Truncated-Type
  is-trunc-type-Connected-Map-Into-Truncated-Type =
    is-trunc-type-Truncated-Type
      truncated-type-Connected-Map-Into-Truncated-Type

  connected-map-Connected-Map-Into-Truncated-Type :
    connected-map k A type-Connected-Map-Into-Truncated-Type
  connected-map-Connected-Map-Into-Truncated-Type = pr2 f

  map-Connected-Map-Into-Truncated-Type :
    A → type-Connected-Map-Into-Truncated-Type
  map-Connected-Map-Into-Truncated-Type =
    map-connected-map connected-map-Connected-Map-Into-Truncated-Type

  is-connected-map-Connected-Map-Into-Truncated-Type :
    is-connected-map k map-Connected-Map-Into-Truncated-Type
  is-connected-map-Connected-Map-Into-Truncated-Type =
    is-connected-map-connected-map
      connected-map-Connected-Map-Into-Truncated-Type
```

## Properties

### Dependent universal property for connected maps

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where

  dependent-universal-property-is-connected-map :
    is-connected-map k f → (P : B → Truncated-Type l3 k) →
    is-equiv (precomp-Π f (λ b → type-Truncated-Type (P b)))
  dependent-universal-property-is-connected-map H P =
    is-equiv-precomp-Π-fiber-condition
      ( λ b → is-equiv-diagonal-is-connected (P b) (H b))
      
  equiv-dependent-universal-property-is-connected-map :
    is-connected-map k f → (P : B → Truncated-Type l3 k) →
    ((b : B) → type-Truncated-Type (P b)) ≃ ((a : A) → type-Truncated-Type (P (f a)))
  pr1 (equiv-dependent-universal-property-is-connected-map H P) =
    precomp-Π f (λ b → type-Truncated-Type (P b))
  pr2 (equiv-dependent-universal-property-is-connected-map H P) =
    dependent-universal-property-is-connected-map H P
```

### A map that satisfies the dependent universal property for connected maps is a connected map

```agda
is-connected-map-dependent-universal-property-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  ({l3 : Level} (P : B → Truncated-Type l3 k) →
    is-equiv (precomp-Π f (λ b → type-Truncated-Type (P b)))) →
  is-connected-map k f
is-connected-map-dependent-universal-property-connected-map k {A = A} {B = B} {f = f} H =
  map-inv-distributive-Π-Σ
    ( c ,
      λ b →
        function-dependent-universal-property-trunc
          ( Id-Truncated-Type' (trunc k (fib f b)) _)
          ( inv-map-reduce-Π-fib
              ( f)
              ( λ b' s → c b' ＝ unit-trunc s)
              ( λ a → htpy-eq (issec-map-inv-equiv e (λ a → unit-trunc (a , refl))) a) b))
  where
    e : ((b : B) → type-trunc k (fib f b))
      ≃ ((a : A) → type-trunc k (fib f (f a)))
    pr1 e = precomp-Π f (λ b → type-trunc k (fib f b))
    pr2 e = H (λ b' → trunc k (fib f b'))

    c : (b : B) → type-trunc k (fib f b)
    c = map-inv-equiv e (λ a → unit-trunc (a , refl))
```

### A map `f : A → B` is `k`-connected if and only if precomposing dependent functions into `k + n`-truncated types is an `n-2`-truncated map for all `n : ℕ`

```agda
is-trunc-map-precomp-Π-is-connected-map :
  {l1 l2 l3 : Level} (k l n : 𝕋) → add-𝕋 k (succ-𝕋 (succ-𝕋 n)) ＝ l →
  {A : UU l1} {B : UU l2} {f : A → B} → is-connected-map k f →
  (P : B → Truncated-Type l3 l) →
  is-trunc-map
    ( n)
    ( precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-connected-map
  {l1} {l2} {l3} k ._ neg-two-𝕋 refl {A} {B} H P =
  is-contr-map-is-equiv
    ( dependent-universal-property-is-connected-map k H
      ( λ b →
        pair
          ( type-Truncated-Type (P b))
          ( is-trunc-eq
            ( right-unit-law-add-𝕋 k)
            ( is-trunc-type-Truncated-Type (P b)))))
is-trunc-map-precomp-Π-is-connected-map k ._ (succ-𝕋 n) refl {A} {B} {f} H P =
  is-trunc-map-succ-precomp-Π
    ( λ g h →
      is-trunc-map-precomp-Π-is-connected-map k _ n refl H
        ( λ b →
          pair
            ( eq-value g h b)
            ( is-trunc-eq
              ( right-successor-law-add-𝕋 k n)
              ( is-trunc-type-Truncated-Type (P b))
              ( g b)
              ( h b))))
```

### Characterization of the identity type of `Connected-Map l2 k A`

```agda
equiv-Connected-Map :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (f g : Connected-Map l2 k A) → UU (l1 ⊔ l2)
equiv-Connected-Map f g =
  Σ ( type-Connected-Map f ≃ type-Connected-Map g)
    ( λ e → (map-equiv e ∘ map-Connected-Map f) ~ map-Connected-Map g)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  id-equiv-Connected-Map : equiv-Connected-Map f f
  pr1 id-equiv-Connected-Map = id-equiv
  pr2 id-equiv-Connected-Map = refl-htpy

  is-contr-total-equiv-Connected-Map :
    is-contr (Σ (Connected-Map l2 k A) (equiv-Connected-Map f))
  is-contr-total-equiv-Connected-Map =
    is-contr-total-Eq-structure
      ( λ Y g e → (map-equiv e ∘ map-Connected-Map f) ~ map-connected-map g)
      ( is-contr-total-equiv (type-Connected-Map f))
      ( pair (type-Connected-Map f) id-equiv)
      ( is-contr-total-htpy-connected-map (connected-map-Connected-Map f))

  equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) → equiv-Connected-Map f g
  equiv-eq-Connected-Map .f refl = id-equiv-Connected-Map

  is-equiv-equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → is-equiv (equiv-eq-Connected-Map g)
  is-equiv-equiv-eq-Connected-Map =
    fundamental-theorem-id
      is-contr-total-equiv-Connected-Map
      equiv-eq-Connected-Map

  extensionality-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) ≃ equiv-Connected-Map f g
  pr1 (extensionality-Connected-Map g) = equiv-eq-Connected-Map g
  pr2 (extensionality-Connected-Map g) = is-equiv-equiv-eq-Connected-Map g

  eq-equiv-Connected-Map :
    (g : Connected-Map l2 k A) → equiv-Connected-Map f g → (f ＝ g)
  eq-equiv-Connected-Map g =
    map-inv-equiv (extensionality-Connected-Map g)
```

### Characterization of the identity type of `Connected-Map-Into-Truncated-Type l2 k A`

```agda
equiv-Connected-Map-Into-Truncated-Type :
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1} →
  (f g : Connected-Map-Into-Truncated-Type l2 k l A) → UU (l1 ⊔ l2)
equiv-Connected-Map-Into-Truncated-Type f g =
  Σ ( type-Connected-Map-Into-Truncated-Type f ≃
      type-Connected-Map-Into-Truncated-Type g)
    ( λ e →
      ( map-equiv e ∘ map-Connected-Map-Into-Truncated-Type f) ~
      ( map-Connected-Map-Into-Truncated-Type g))

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  id-equiv-Connected-Map-Into-Truncated-Type :
    equiv-Connected-Map-Into-Truncated-Type f f
  pr1 id-equiv-Connected-Map-Into-Truncated-Type = id-equiv
  pr2 id-equiv-Connected-Map-Into-Truncated-Type = refl-htpy

  is-contr-total-equiv-Connected-Map-Into-Truncated-Type :
    is-contr
      ( Σ ( Connected-Map-Into-Truncated-Type l2 k l A)
          ( equiv-Connected-Map-Into-Truncated-Type f))
  is-contr-total-equiv-Connected-Map-Into-Truncated-Type =
    is-contr-total-Eq-structure
      ( λ Y g e →
        ( map-equiv e ∘ map-Connected-Map-Into-Truncated-Type f) ~
        ( map-connected-map g))
      ( is-contr-total-equiv-Truncated-Type
        ( truncated-type-Connected-Map-Into-Truncated-Type f))
      ( pair (truncated-type-Connected-Map-Into-Truncated-Type f) id-equiv)
      ( is-contr-total-htpy-connected-map
        ( connected-map-Connected-Map-Into-Truncated-Type f))

  equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) → equiv-Connected-Map-Into-Truncated-Type f g
  equiv-eq-Connected-Map-Into-Truncated-Type .f refl =
    id-equiv-Connected-Map-Into-Truncated-Type

  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    is-equiv (equiv-eq-Connected-Map-Into-Truncated-Type g)
  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type =
    fundamental-theorem-id
      is-contr-total-equiv-Connected-Map-Into-Truncated-Type
      equiv-eq-Connected-Map-Into-Truncated-Type

  extensionality-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) ≃ equiv-Connected-Map-Into-Truncated-Type f g
  pr1 (extensionality-Connected-Map-Into-Truncated-Type g) =
    equiv-eq-Connected-Map-Into-Truncated-Type g
  pr2 (extensionality-Connected-Map-Into-Truncated-Type g) =
    is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type g

  eq-equiv-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
      equiv-Connected-Map-Into-Truncated-Type f g → (f ＝ g)
  eq-equiv-Connected-Map-Into-Truncated-Type g =
    map-inv-equiv (extensionality-Connected-Map-Into-Truncated-Type g)
```

### Any map is `(-2)`-connected

```agda
is-connected-map-neg-two-𝕋 :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-connected-map neg-two-𝕋 f
is-connected-map-neg-two-𝕋 f b = is-trunc-type-trunc
```

### An equivalence is a `k`-connected map for any `k`

```agda
is-connected-map-is-equiv :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {f : A → B} → is-equiv f → is-connected-map k f
is-connected-map-is-equiv k H b =
  is-connected-is-contr k (is-contr-map-is-equiv H b)
```

### The composition of two `k`-connected maps is `k`-connected

```agda
is-connected-map-comp :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  {f : A → B} {g : B → C} →
  is-connected-map k f → is-connected-map k g →
  is-connected-map k (g ∘ f)
is-connected-map-comp k {f = f} {g = g} H K c =
  is-connected-equiv
    ( k)
    ( equiv-compute-fib-comp g f c)
    ( is-connected-Σ k (K c) (λ (b , _) → H b))
```

### The total map induced by a family of maps is `k`-connected if and only if all maps in the family are `k`-connected

```agda
module _ {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  is-connected-map-tot-is-fiberwise-connected-map :
    ((x : A) → is-connected-map k (f x)) →
    is-connected-map k (tot f)
  is-connected-map-tot-is-fiberwise-connected-map H (x , y) =
    is-connected-equiv k (compute-fib-tot f (x , y)) (H x y)

  is-fiberwise-connected-map-is-connected-map-tot :
    is-connected-map k (tot f) →
    (x : A) → is-connected-map k (f x)
  is-fiberwise-connected-map-is-connected-map-tot H x y =
    is-connected-equiv k (inv-compute-fib-tot f (x , y)) (H (x , y))
```

### The map `unit-trunc {k}` is `k`-connected

```agda
is-connected-map-unit-trunc :
  {l1 : Level} (k : 𝕋) {A : UU l1} →
  is-connected-map k (unit-trunc {k = k} {A = A})
is-connected-map-unit-trunc k =
  is-connected-map-dependent-universal-property-connected-map k
    dependent-universal-property-trunc
```

### The type `Connected-Map-Into-Truncated-Type l2 k k A` is contractible

### The type `Connected-Map-Into-Truncated-Type l2 k l A` is `k - l - 2` truncated
