# The univalence axiom

```agda
module foundation-core.univalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The {{#concept "univalence axiom" Disambiguation="types" Agda=univalence-axiom}}
characterizes the [identity types](foundation-core.identity-types.md) of
universes. It asserts that the map `(A ＝ B) → (A ≃ B)` is an equivalence.

In this file, we define the statement of the axiom. The axiom itself is
postulated in [`foundation.univalence`](foundation.univalence.md) as
`univalence`.

Univalence is postulated by stating that the canonical comparison map

```text
  equiv-eq : A ＝ B → A ≃ B
```

from identifications between two types to equivalences between them is an
equivalence. Although we could define `equiv-eq` by pattern matching, due to
computational considerations, we define it as

```text
  equiv-eq := equiv-tr (id_𝒰).
```

It follows from this definition that `equiv-eq refl ≐ id-equiv`, as expected.

## Definitions

### Equalities induce equivalences

```agda
module _
  {l : Level}
  where

  equiv-eq : {A B : UU l} → A ＝ B → A ≃ B
  equiv-eq = equiv-tr id

  map-eq : {A B : UU l} → A ＝ B → A → B
  map-eq = map-equiv ∘ equiv-eq

  map-inv-eq : {A B : UU l} → A ＝ B → B → A
  map-inv-eq = map-eq ∘ inv

  compute-equiv-eq-refl :
    {A : UU l} → equiv-eq (refl {x = A}) ＝ id-equiv
  compute-equiv-eq-refl = refl
```

### The statement of the univalence axiom

#### An instance of univalence

```agda
instance-univalence : {l : Level} (A B : UU l) → UU (lsuc l)
instance-univalence A B = is-equiv (equiv-eq {A = A} {B = B})
```

#### Based univalence

```agda
based-univalence-axiom : {l : Level} (A : UU l) → UU (lsuc l)
based-univalence-axiom {l} A = (B : UU l) → instance-univalence A B
```

#### The univalence axiom with respect to a universe level

```agda
univalence-axiom-Level : (l : Level) → UU (lsuc l)
univalence-axiom-Level l = (A B : UU l) → instance-univalence A B
```

#### The univalence axiom

```agda
univalence-axiom : UUω
univalence-axiom = {l : Level} → univalence-axiom-Level l
```

## Properties

### The univalence axiom implies that the total space of equivalences is contractible

```agda
abstract
  is-torsorial-equiv-based-univalence :
    {l : Level} (A : UU l) →
    based-univalence-axiom A → is-torsorial (λ (B : UU l) → A ≃ B)
  is-torsorial-equiv-based-univalence A =
    fundamental-theorem-id' (λ B → equiv-eq)
```

### Contractibility of the total space of equivalences implies univalence

```agda
abstract
  based-univalence-is-torsorial-equiv :
    {l : Level} (A : UU l) →
    is-torsorial (λ (B : UU l) → A ≃ B) → based-univalence-axiom A
  based-univalence-is-torsorial-equiv A c =
    fundamental-theorem-id c (λ B → equiv-eq)
```

### The underlying map of `equiv-eq` evaluated at `ap B` is the same as transport in the family `B`

For any type family `B` and identification `p : x ＝ y` in the base, we have a
commuting diagram

```text
                 equiv-eq
    (B x = B y) ---------> (B x ≃ B y)
         ∧                      |
  ap B p |                      | map-equiv
         |                      ∨
      (x = y) -----------> (B x → B y).
                  tr B p
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  where

  compute-equiv-eq-ap :
    (p : x ＝ y) → equiv-eq (ap B p) ＝ equiv-tr B p
  compute-equiv-eq-ap refl = refl

  compute-map-eq-ap :
    (p : x ＝ y) → map-eq (ap B p) ＝ tr B p
  compute-map-eq-ap p = ap map-equiv (compute-equiv-eq-ap p)
```
