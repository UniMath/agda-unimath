# Impredicative encodings of the logical operations

```agda
module foundation.impredicative-encodings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

By quantifying over all propositions in a universe, we can define all the
logical operations. The idea is to use the fact that any proposition `P` is
equivalent to the proposition `(Q : Prop l) → (P ⇒ Q) ⇒ Q`, which can be thought
of as the least proposition `Q` containing `P`.

### The impredicative encoding of the propositional truncation

```agda
impredicative-trunc-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-trunc-Prop {l} A =
  Π-Prop
    ( Prop l)
    ( λ Q → function-Prop (A → type-Prop Q) Q)

type-impredicative-trunc-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-trunc-Prop {l} A =
  type-Prop (impredicative-trunc-Prop A)

map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A → type-impredicative-trunc-Prop A
map-impredicative-trunc-Prop {l} A =
  map-universal-property-trunc-Prop
    ( impredicative-trunc-Prop A)
    ( λ x Q f → f x)

inv-map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-trunc-Prop A → type-trunc-Prop A
inv-map-impredicative-trunc-Prop A H =
  H (trunc-Prop A) unit-trunc-Prop

equiv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A ≃ type-impredicative-trunc-Prop A
equiv-impredicative-trunc-Prop A =
  equiv-iff
    ( trunc-Prop A)
    ( impredicative-trunc-Prop A)
    ( map-impredicative-trunc-Prop A)
    ( inv-map-impredicative-trunc-Prop A)
```

### The impredicative encoding of conjunction

```agda
impredicative-conj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-conj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( Prop (l1 ⊔ l2))
    ( λ Q → function-Prop (type-Prop P1 → (type-Prop P2 → type-Prop Q)) Q)

type-impredicative-conj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-conj-Prop P1 P2 =
  type-Prop (impredicative-conj-Prop P1 P2)

map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-conj-Prop P1 P2 → type-impredicative-conj-Prop P1 P2
map-impredicative-conj-Prop {l1} {l2} P1 P2 (pair p1 p2) Q f =
  f p1 p2

inv-map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-conj-Prop P1 P2 → type-conj-Prop P1 P2
inv-map-impredicative-conj-Prop P1 P2 H =
  H (conj-Prop P1 P2) (λ p1 p2 → pair p1 p2)

equiv-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-conj-Prop P1 P2 ≃ type-impredicative-conj-Prop P1 P2
equiv-impredicative-conj-Prop P1 P2 =
  equiv-iff
    ( conj-Prop P1 P2)
    ( impredicative-conj-Prop P1 P2)
    ( map-impredicative-conj-Prop P1 P2)
    ( inv-map-impredicative-conj-Prop P1 P2)
```

### The impredicative encoding of disjunction

```agda
impredicative-disj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-disj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( Prop (l1 ⊔ l2))
    ( λ Q →
      function-Prop
        ( type-implication-Prop P1 Q)
        ( function-Prop (type-implication-Prop P2 Q) Q))

type-impredicative-disj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-disj-Prop P1 P2 =
  type-Prop (impredicative-disj-Prop P1 P2)

map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disj-Prop P1 P2 → type-impredicative-disj-Prop P1 P2
map-impredicative-disj-Prop {l1} {l2} P1 P2 =
  map-universal-property-trunc-Prop
    ( impredicative-disj-Prop P1 P2)
    ( ind-coprod
      ( λ x → type-impredicative-disj-Prop P1 P2)
      ( λ x Q f1 f2 → f1 x)
      ( λ y Q f1 f2 → f2 y))

inv-map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-disj-Prop P1 P2 → type-disj-Prop P1 P2
inv-map-impredicative-disj-Prop P1 P2 H =
  H (disj-Prop P1 P2) (inl-disj-Prop P1 P2) (inr-disj-Prop P1 P2)

equiv-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disj-Prop P1 P2 ≃ type-impredicative-disj-Prop P1 P2
equiv-impredicative-disj-Prop P1 P2 =
  equiv-iff
    ( disj-Prop P1 P2)
    ( impredicative-disj-Prop P1 P2)
    ( map-impredicative-disj-Prop P1 P2)
    ( inv-map-impredicative-disj-Prop P1 P2)
```

### The impredicative encoding of negation

```agda
impredicative-neg-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-neg-Prop {l} A =
  Π-Prop (Prop l) (λ Q → function-Prop A Q)

type-impredicative-neg-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-neg-Prop A =
  type-Prop (impredicative-neg-Prop A)

map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A → type-impredicative-neg-Prop A
map-impredicative-neg-Prop A f Q a = ex-falso (f a)

inv-map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-neg-Prop A → ¬ A
inv-map-impredicative-neg-Prop A H a = H (neg-Prop' A) a a

equiv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A ≃ type-impredicative-neg-Prop A
equiv-impredicative-neg-Prop A =
  equiv-iff
    ( neg-Prop' A)
    ( impredicative-neg-Prop A)
    ( map-impredicative-neg-Prop A)
    ( inv-map-impredicative-neg-Prop A)
```

### The impredicative encoding of existential quantification

```agda
impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → Prop (lsuc (l1 ⊔ l2))
impredicative-exists-Prop {l1} {l2} {A} P =
  Π-Prop
    ( Prop (l1 ⊔ l2))
    ( λ Q → function-Prop ((x : A) → type-Prop (P x) → type-Prop Q) Q)

type-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → UU (lsuc (l1 ⊔ l2))
type-impredicative-exists-Prop P =
  type-Prop (impredicative-exists-Prop P)

map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P → type-impredicative-exists-Prop P
map-impredicative-exists-Prop {l1} {l2} {A} P =
  map-universal-property-trunc-Prop
    ( impredicative-exists-Prop P)
    ( ind-Σ (λ x y Q h → h x y))

inv-map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  type-impredicative-exists-Prop P → exists A P
inv-map-impredicative-exists-Prop {A = A} P H =
  H ( exists-Prop A P)
    ( λ x y → unit-trunc-Prop (pair x y))

equiv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P ≃ type-impredicative-exists-Prop P
equiv-impredicative-exists-Prop {A = A} P =
  equiv-iff
    ( exists-Prop A P)
    ( impredicative-exists-Prop P)
    ( map-impredicative-exists-Prop P)
    ( inv-map-impredicative-exists-Prop P)
```

### The impredicative encoding of the based identity type of a set

```agda
impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → Prop (lsuc l)
impredicative-based-id-Prop {l} A a x =
  Π-Prop (type-Set A → Prop l) (λ Q → hom-Prop (Q a) (Q x))

type-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → UU (lsuc l)
type-impredicative-based-id-Prop A a x =
  type-Prop (impredicative-based-id-Prop A a x)

map-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  a ＝ x → type-impredicative-based-id-Prop A a x
map-impredicative-based-id-Prop A a .a refl Q p = p

inv-map-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  type-impredicative-based-id-Prop A a x → a ＝ x
inv-map-impredicative-based-id-Prop A a x H =
  H (λ x → pair (a ＝ x) (is-set-type-Set A a x)) refl

equiv-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  (a ＝ x) ≃ type-impredicative-based-id-Prop A a x
equiv-impredicative-based-id-Prop A a x =
  equiv-iff
    ( pair (a ＝ x) (is-set-type-Set A a x))
    ( impredicative-based-id-Prop A a x)
    ( map-impredicative-based-id-Prop A a x)
    ( inv-map-impredicative-based-id-Prop A a x)
```

### The impredicative encoding of Martin-Löf's identity type of a set

```agda
impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → Prop (lsuc l)
impredicative-id-Prop {l} A x y =
  Π-Prop (type-Set A → type-Set A → Prop l)
    (λ Q → function-Prop ((a : type-Set A) → type-Prop (Q a a)) (Q x y))

type-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → UU (lsuc l)
type-impredicative-id-Prop A x y =
  type-Prop (impredicative-id-Prop A x y)

map-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  x ＝ y → type-impredicative-id-Prop A x y
map-impredicative-id-Prop A x .x refl Q r = r x

inv-map-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  type-impredicative-id-Prop A x y → x ＝ y
inv-map-impredicative-id-Prop A x y H =
  H (λ a b → pair (a ＝ b) (is-set-type-Set A a b)) (λ a → refl)

equiv-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  (x ＝ y) ≃ type-impredicative-id-Prop A x y
equiv-impredicative-id-Prop A x y =
  equiv-iff
    ( pair (x ＝ y) (is-set-type-Set A x y))
    ( impredicative-id-Prop A x y)
    ( map-impredicative-id-Prop A x y)
    ( inv-map-impredicative-id-Prop A x y)
```
