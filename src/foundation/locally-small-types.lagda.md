# Locally small types

```agda
module foundation.locally-small-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.inhabited-subtypes
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be
{{#concept "locally small" Disambiguation="type" Agda=is-locally-small}} with
respect to a [universe](foundation.universe-levels.md) `UU l` if its
[identity types](foundation-core.identity-types.md) are
[small](foundation-core.small-types.md) with respect to that universe.

## Definition

### Locally small types

```agda
is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (x ＝ y)

module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A) (x y : A)
  where

  type-is-locally-small : UU l
  type-is-locally-small = pr1 (H x y)

  equiv-is-locally-small : (x ＝ y) ≃ type-is-locally-small
  equiv-is-locally-small = pr2 (H x y)

  inv-equiv-is-locally-small : type-is-locally-small ≃ (x ＝ y)
  inv-equiv-is-locally-small = inv-equiv equiv-is-locally-small

  map-equiv-is-locally-small : (x ＝ y) → type-is-locally-small
  map-equiv-is-locally-small = map-equiv equiv-is-locally-small

  map-inv-equiv-is-locally-small : type-is-locally-small → (x ＝ y)
  map-inv-equiv-is-locally-small = map-inv-equiv equiv-is-locally-small
```

### The subuniverse of `UU l1`-locally small types in `UU l2`

```agda
Locally-Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Locally-Small-Type l1 l2 = Σ (UU l2) (is-locally-small l1)

module _
  {l1 l2 : Level} (A : Locally-Small-Type l1 l2)
  where

  type-Locally-Small-Type : UU l2
  type-Locally-Small-Type = pr1 A

  is-locally-small-type-Locally-Small-Type :
    is-locally-small l1 type-Locally-Small-Type
  is-locally-small-type-Locally-Small-Type = pr2 A

  small-identity-type-Locally-Small-Type :
    (x y : type-Locally-Small-Type) → UU l1
  small-identity-type-Locally-Small-Type =
    type-is-locally-small is-locally-small-type-Locally-Small-Type

  equiv-is-locally-small-type-Locally-Small-Type :
    (x y : type-Locally-Small-Type) →
    (x ＝ y) ≃ small-identity-type-Locally-Small-Type x y
  equiv-is-locally-small-type-Locally-Small-Type =
    equiv-is-locally-small is-locally-small-type-Locally-Small-Type
```

## Properties

### Being locally small is a property

```agda
is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (x ＝ y)))

is-locally-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → Prop (lsuc l ⊔ l1)
pr1 (is-locally-small-Prop l A) = is-locally-small l A
pr2 (is-locally-small-Prop l A) = is-prop-is-locally-small l A
```

### Any type in `UU l` is `l`-locally small

```agda
is-locally-small' : {l : Level} {A : UU l} → is-locally-small l A
is-locally-small' x y = is-small'
```

### Locally small types are closed under embeddings

```agda
is-locally-small-emb :
  {l1 l2 l : Level} {A : UU l1} {B : UU l2} →
  A ↪ B → is-locally-small l B → is-locally-small l A
is-locally-small-emb f H x y =
  is-small-equiv
    ( map-emb f x ＝ map-emb f y)
    ( equiv-ap-emb f)
    ( H (map-emb f x) (map-emb f y))
```

### Locally small types are closed under equivalences

```agda
is-locally-small-equiv :
  {l1 l2 l : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-locally-small l B → is-locally-small l A
is-locally-small-equiv e = is-locally-small-emb (emb-equiv e)
```

### Any small type is locally small

```agda
is-locally-small-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → is-locally-small l A
pr1 (is-locally-small-is-small (X , e) x y) =
  map-equiv e x ＝ map-equiv e y
pr2 (is-locally-small-is-small (X , e) x y) = equiv-ap e x y
```

### Any proposition is locally small

```agda
is-locally-small-is-prop :
  (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
is-locally-small-is-prop l H x y = is-small-is-contr l (H x y)
```

### Any univalent universe is locally small

```agda
is-locally-small-UU :
  {l : Level} → is-locally-small l (UU l)
pr1 (is-locally-small-UU X Y) = X ≃ Y
pr2 (is-locally-small-UU X Y) = equiv-univalence
```

### Any Σ-type of locally small types is locally small

```agda
is-locally-small-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-locally-small l3 A → ((x : A) → is-locally-small l4 (B x)) →
  is-locally-small (l3 ⊔ l4) (Σ A B)
is-locally-small-Σ {B = B} H K x y =
  is-small-equiv
    ( Eq-Σ x y)
    ( equiv-pair-eq-Σ x y)
    ( is-small-Σ
      ( H (pr1 x) (pr1 y))
      ( λ p → K (pr1 y) (tr B p (pr2 x)) (pr2 y)))

Σ-Locally-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Locally-Small-Type l1 l2) →
  (type-Locally-Small-Type A → Locally-Small-Type l3 l4) →
  Locally-Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Σ-Locally-Small-Type A B) =
  Σ (type-Locally-Small-Type A) (type-Locally-Small-Type ∘ B)
pr2 (Σ-Locally-Small-Type A B) =
  is-locally-small-Σ
    ( is-locally-small-type-Locally-Small-Type A)
    ( is-locally-small-type-Locally-Small-Type ∘ B)
```

### The underlying type of a subtype of a locally small type is locally small

```agda
is-locally-small-type-subtype :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) →
  is-locally-small l3 A → is-locally-small l3 (type-subtype P)
is-locally-small-type-subtype {l3 = l3} P H =
  is-locally-small-Σ H
    ( λ a → is-locally-small-is-prop l3 (is-prop-is-in-subtype P a))

type-subtype-Locally-Small-Type :
  {l1 l2 l3 : Level} (A : Locally-Small-Type l1 l2) →
  subtype l3 (type-Locally-Small-Type A) → Locally-Small-Type l1 (l2 ⊔ l3)
pr1 (type-subtype-Locally-Small-Type A P) = type-subtype P
pr2 (type-subtype-Locally-Small-Type A P) =
  is-locally-small-type-subtype P (is-locally-small-type-Locally-Small-Type A)
```

### Any product of locally small types indexed by a small type is small

```agda
is-locally-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-locally-small l4 (B x)) →
  is-locally-small (l3 ⊔ l4) ((x : A) → B x)
is-locally-small-Π H K f g =
  is-small-equiv
    ( f ~ g)
    ( equiv-funext)
    ( is-small-Π H (λ x → K x (f x) (g x)))

Π-Locally-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Locally-Small-Type l3 l4) →
  Locally-Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Locally-Small-Type A B) =
  (a : type-Small-Type A) → type-Locally-Small-Type (B a)
pr2 (Π-Locally-Small-Type A B) =
  is-locally-small-Π
    ( is-small-type-Small-Type A)
    ( is-locally-small-type-Locally-Small-Type ∘ B)
```

### The type of types in any given subuniverse is locally small

```agda
is-locally-small-type-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  is-locally-small l1 (type-subuniverse P)
is-locally-small-type-subuniverse P =
  is-locally-small-type-subtype P is-locally-small-UU
```

### The type of locally small types is locally small

```agda
is-locally-small-Locally-Small-Type :
  {l1 l2 : Level} → is-locally-small l2 (Locally-Small-Type l1 l2)
is-locally-small-Locally-Small-Type {l1} =
  is-locally-small-type-subuniverse (is-locally-small-Prop l1)
```

### The type of truncated types is locally small

```agda
is-locally-small-Truncated-Type :
  {l : Level} (k : 𝕋) → is-locally-small l (Truncated-Type l k)
is-locally-small-Truncated-Type k =
  is-locally-small-type-subuniverse (is-trunc-Prop k)
```

### The type of propositions is locally small

```agda
is-locally-small-type-Prop :
  {l : Level} → is-locally-small l (Prop l)
is-locally-small-type-Prop = is-locally-small-Truncated-Type neg-one-𝕋
```

### The type of subtypes of a small type is locally small

```agda
is-locally-small-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  is-small l2 A → is-locally-small (l2 ⊔ l3) (subtype l3 A)
is-locally-small-subtype H =
  is-locally-small-Π H (λ _ → is-locally-small-type-Prop)
```

### The type of inhabited subtypes of a small type is locally small

```agda
is-locally-small-inhabited-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  is-small l2 A → is-locally-small (l2 ⊔ l3) (inhabited-subtype l3 A)
is-locally-small-inhabited-subtype H =
  is-locally-small-type-subtype
    ( is-inhabited-subtype-Prop)
    ( is-locally-small-subtype H)
```

## See also

- [The replacement axiom](foundation.replacement.md)

## References

- Theorem 4.6 in {{#cite Rij17}}.
- Section 2.19 in {{#cite SymmetryBook}}.

{{#bibliography}}
