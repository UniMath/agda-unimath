# 0-Connected types

```agda
module foundation.0-connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels
```

</details>

## Idea

A type is said to be connected if its type of connected components, i.e., its set truncation, is contractible.

```agda
is-0-connected-Prop : {l : Level} → UU l → Prop l
is-0-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-0-connected : {l : Level} → UU l → UU l
is-0-connected A = type-Prop (is-0-connected-Prop A)

is-prop-is-0-connected : {l : Level} (A : UU l) → is-prop (is-0-connected A)
is-prop-is-0-connected A = is-prop-type-Prop (is-0-connected-Prop A)

abstract
  is-inhabited-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → is-inhabited A
  is-inhabited-is-0-connected {l} {A} C =
    apply-universal-property-trunc-Set'
      ( center C)
      ( set-Prop (trunc-Prop A))
      ( unit-trunc-Prop)

abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → (x y : A) → mere-eq x y
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)

abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

is-0-connected-is-surjective-pt :
  {l1 : Level} {A : UU l1} (a : A) →
  is-surjective (pt a) → is-0-connected A
is-0-connected-is-surjective-pt a H =
  is-0-connected-mere-eq a
    ( λ x →
      apply-universal-property-trunc-Prop
        ( H x)
        ( mere-eq-Prop a x)
        ( λ u → unit-trunc-Prop (pr2 u)))

is-surjective-pt-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) →
  is-0-connected A → is-surjective (pt a)
is-surjective-pt-is-0-connected a H x =
  apply-universal-property-trunc-Prop
    ( mere-eq-is-0-connected H a x)
    ( trunc-Prop (fib (pt a) x))
    ( λ {refl → unit-trunc-Prop (pair star refl)})

is-trunc-map-ev-pt-is-connected :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
  is-0-connected A → is-trunc (succ-𝕋 k) B →
  is-trunc-map k (ev-pt a (λ _ → B))
is-trunc-map-ev-pt-is-connected k {A} {B} a H K =
  is-trunc-map-comp k
    ( ev-pt star (λ _ → B))
    ( precomp (pt a) B)
    ( is-trunc-map-is-equiv k
      ( universal-property-contr-is-contr star is-contr-unit B))
    ( is-trunc-map-precomp-Π-is-surjective k
      ( is-surjective-pt-is-0-connected a H)
      ( λ _ → pair B K))

equiv-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  ( {l : Level} (P : A → Prop l) →
    ((x : A) → type-Prop (P x)) ≃ type-Prop (P a))
equiv-dependent-universal-property-is-0-connected a H P =
  ( equiv-universal-property-unit (type-Prop (P a))) ∘e
  ( equiv-dependent-universal-property-surj-is-surjective
    ( pt a)
    ( is-surjective-pt-is-0-connected a H)
    ( P))

apply-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  {l : Level} (P : A → Prop l) → type-Prop (P a) → (x : A) → type-Prop (P x)
apply-dependent-universal-property-is-0-connected a H P =
  map-inv-equiv (equiv-dependent-universal-property-is-0-connected a H P)

abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-0-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (pair x b) =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected C a x)
      ( trunc-Prop (fib (fiber-inclusion B a) (pair x b)))
      ( λ { refl → unit-trunc-Prop (pair b refl)})

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x =
    apply-universal-property-trunc-Prop
      ( H (λ x → unit) (pair x star))
      ( mere-eq-Prop a x)
      ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

abstract
  is-0-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-0-connected A
  is-0-connected-is-surjective-fiber-inclusion a H =
    is-0-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)

is-0-connected-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected B → is-0-connected A
is-0-connected-equiv e = is-contr-equiv _ (equiv-trunc-Set e)

is-0-connected-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected A → is-0-connected B
is-0-connected-equiv' e = is-0-connected-equiv (inv-equiv e)
```
