# `K`-Connected types, with respect to a subuniverse `K`

```agda
module orthogonal-factorization-systems.connected-types-at-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.retracts-of-arrows
open import foundation.retracts-of-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes

open import orthogonal-factorization-systems.equivalences-at-subuniverses
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, a type `A` is said to be
{{#concept "`K`-connected" Disambiguation="type, with respect to a subuniverse" Agda=is-subuniverse-connected}}
if it satisfies the
{{#concept "universal property" Disambiguation="subuniverse connected types"}}
of `K`-connected types:

For every `U` in `K`, the [diagonal map](foundation.diagonal-maps-of-types.md)

```text
 U → (A → U)
```

is an [equivalence](foundation-core.equivalences.md).

Equivalently, a type is `K`-connected if

1. Its [terminal projection map](foundation.unit-type.md) is a
   `K`-[equivalence](orthogonal-factorization-systems.equivalences-at-subuniverses.md).
2. For every `U` in `K` and `u : A → U` there
   [uniquely exists](foundation.uniqueness-quantification.md) an element `v : U`
   and a [homotopy](foundation-core.homotopies.md) `const v ~ u`. I.e., every
   function out of `A` into a `K`-type is uniquely constant.

## Definitions

### The predicate on types of being `K`-connected

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) (A : UU l3)
  where

  is-subuniverse-connected-Prop : Prop (lsuc l1 ⊔ l2 ⊔ l3)
  is-subuniverse-connected-Prop =
    Π-Prop
      ( type-subuniverse K)
      ( λ U → is-equiv-Prop (diagonal-exponential (pr1 U) A))

  is-subuniverse-connected : UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-subuniverse-connected =
    (U : type-subuniverse K) → is-equiv (diagonal-exponential (pr1 U) A)

  is-prop-is-subuniverse-connected :
    is-prop is-subuniverse-connected
  is-prop-is-subuniverse-connected =
    is-prop-type-Prop is-subuniverse-connected-Prop
```

### The universe of `K`-connected types

```agda
subuniverse-connected-type :
  {l1 l2 : Level} (l3 : Level) (K : subuniverse l1 l2) →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
subuniverse-connected-type l3 K =
  type-subtype (is-subuniverse-connected-Prop {l3 = l3} K)

module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2)
  where

  type-subuniverse-connected-type : subuniverse-connected-type l3 K → UU l3
  type-subuniverse-connected-type =
    inclusion-subtype (is-subuniverse-connected-Prop K)

  is-subuniverse-connected-type-subuniverse-connected-type :
    (A : subuniverse-connected-type l3 K) →
    is-subuniverse-connected K (type-subuniverse-connected-type A)
  is-subuniverse-connected-type-subuniverse-connected-type =
    is-in-subtype-inclusion-subtype (is-subuniverse-connected-Prop K)

  emb-inclusion-subuniverse-connected-type :
    subuniverse-connected-type l3 K ↪ UU l3
  emb-inclusion-subuniverse-connected-type =
    emb-subtype (is-subuniverse-connected-Prop K)
```

### The constancy condition of `K`-connected types

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) (A : UU l3)
  where

  is-subuniverse-connected-const-condition :
    UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-subuniverse-connected-const-condition =
    (U : type-subuniverse K) (u : A → pr1 U) →
    is-contr (Σ (pr1 U) (λ v → (x : A) → v ＝ u x))

  abstract
    is-prop-is-subuniverse-connected-const-condition :
      is-prop is-subuniverse-connected-const-condition
    is-prop-is-subuniverse-connected-const-condition =
      is-prop-Π (λ U → is-prop-Π (λ u → is-property-is-contr))

  is-subuniverse-connected-const-condition-Prop :
    Prop (lsuc l1 ⊔ l2 ⊔ l3)
  is-subuniverse-connected-const-condition-Prop =
    ( is-subuniverse-connected-const-condition ,
      is-prop-is-subuniverse-connected-const-condition)
```

## Properties

### A type is `K`-connected if and only if the terminal map is a `K`-equivalence

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) {A : UU l3}
  where

  is-subuniverse-connected-is-subuniverse-equiv-terminal-map :
    is-subuniverse-equiv K (terminal-map A) →
    is-subuniverse-connected K A
  is-subuniverse-connected-is-subuniverse-equiv-terminal-map H U =
    is-equiv-diagonal-exponential-is-equiv-precomp-terminal-map (H U)

  is-subuniverse-equiv-terminal-map-is-subuniverse-connected :
    is-subuniverse-connected K A →
    is-subuniverse-equiv K (terminal-map A)
  is-subuniverse-equiv-terminal-map-is-subuniverse-connected H U =
    is-equiv-precomp-terminal-map-is-equiv-diagonal-exponential (H U)
```

### A type is `K`-connected if and only if it satisfies the constancy condition

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) {A : UU l3}
  where

  abstract
    is-subuniverse-connected-is-subuniverse-connected-const-condition :
      is-subuniverse-connected-const-condition K A →
      is-subuniverse-connected K A
    is-subuniverse-connected-is-subuniverse-connected-const-condition H U =
      is-equiv-is-contr-map
        ( λ u →
          is-contr-equiv
            ( Σ (pr1 U) (λ v → (x : A) → v ＝ u x))
            ( compute-fiber-diagonal-exponential u)
            ( H U u))

  abstract
    is-subuniverse-connected-const-condition-is-subuniverse-connected :
      is-subuniverse-connected K A →
      is-subuniverse-connected-const-condition K A
    is-subuniverse-connected-const-condition-is-subuniverse-connected H U u =
      is-contr-equiv'
        ( fiber (diagonal-exponential (pr1 U) A) u)
        ( compute-fiber-diagonal-exponential u)
        ( is-contr-map-is-equiv (H U) u)
```

### All types are `Contr`-connected

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-Contr-connected : is-subuniverse-connected (is-contr-Prop {l2}) A
  is-Contr-connected U = is-equiv-diagonal-exponential-is-contr' (pr2 U) A
```

### Contractible types are `K`-connected

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) {A : UU l3}
  where

  is-subuniverse-connected-is-contr :
    is-contr A → is-subuniverse-connected K A
  is-subuniverse-connected-is-contr H U =
    is-equiv-diagonal-exponential-is-contr H (pr1 U)
```

### `K`-connected types are closed under retracts

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  where

  is-subuniverse-connected-retract :
    A retract-of B →
    is-subuniverse-connected K B →
    is-subuniverse-connected K A
  is-subuniverse-connected-retract R H U =
    is-equiv-retract-arrow-is-equiv
      ( diagonal-exponential (pr1 U) A)
      ( diagonal-exponential (pr1 U) B)
      ( retract-arrow-diagonal-exponential-retract id-retract R)
      ( H U)
```

### `K`-connected types are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  where

  is-subuniverse-connected-equiv :
    A ≃ B →
    is-subuniverse-connected K B →
    is-subuniverse-connected K A
  is-subuniverse-connected-equiv e =
    is-subuniverse-connected-retract K (retract-equiv e)

  is-subuniverse-connected-equiv' :
    A ≃ B →
    is-subuniverse-connected K A →
    is-subuniverse-connected K B
  is-subuniverse-connected-equiv' e =
    is-subuniverse-connected-retract K (retract-inv-equiv e)
```

### `K`-connected types are closed under `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  where

  is-subuniverse-connected-is-subuniverse-equiv :
    (f : A → B) → is-subuniverse-equiv K f →
    is-subuniverse-connected K B → is-subuniverse-connected K A
  is-subuniverse-connected-is-subuniverse-equiv f F H =
    is-subuniverse-connected-is-subuniverse-equiv-terminal-map K
      ( is-subuniverse-equiv-comp K (terminal-map B) f F
        ( is-subuniverse-equiv-terminal-map-is-subuniverse-connected K H))

  is-subuniverse-connected-is-subuniverse-equiv' :
    (f : A → B) → is-subuniverse-equiv K f →
    is-subuniverse-connected K A → is-subuniverse-connected K B
  is-subuniverse-connected-is-subuniverse-equiv' f F H =
    is-subuniverse-connected-is-subuniverse-equiv-terminal-map K
      ( is-subuniverse-equiv-left-factor K (terminal-map B) f
        ( is-subuniverse-equiv-terminal-map-is-subuniverse-connected K H)
        ( F))

  is-subuniverse-connected-subuniverse-equiv :
    subuniverse-equiv K A B →
    is-subuniverse-connected K B →
    is-subuniverse-connected K A
  is-subuniverse-connected-subuniverse-equiv (f , F) =
    is-subuniverse-connected-is-subuniverse-equiv f F

  is-subuniverse-connected-subuniverse-equiv' :
    subuniverse-equiv K A B →
    is-subuniverse-connected K A →
    is-subuniverse-connected K B
  is-subuniverse-connected-subuniverse-equiv' (f , F) =
    is-subuniverse-connected-is-subuniverse-equiv' f F
```
