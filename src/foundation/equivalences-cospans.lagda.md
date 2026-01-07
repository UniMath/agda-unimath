# Equivalences of cospans

```agda
module foundation.equivalences-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-cospans
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An {{#concept "equivalence of cospans" Agda=equiv-cospan}} from
[cospans](foundation.cospans.md) `(X , f , g)` to `(Y , h , k)` between types
`A` and `B` consists of an [equivalence](foundation-core.equivalences.md)
`e : X ≃ Y` such that the triangles

```text
      e              e
  X ----> Y      X ----> Y
   \     /        \     /
  f \   / h      g \   / k
     ∨ ∨            ∨ ∨
      A              B
```

both [commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### The predicate of being an equivalence of cospans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : cospan l3 A B) (t : cospan l4 A B)
  where

  is-equiv-hom-cospan : hom-cospan s t → UU (l3 ⊔ l4)
  is-equiv-hom-cospan f = is-equiv (map-hom-cospan s t f)
```

### Equivalences of cospans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : cospan l3 A B) (t : cospan l4 A B)
  where

  equiv-cospan : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-cospan =
    Σ ( cospanning-type-cospan s ≃ cospanning-type-cospan t)
      ( λ e → coherence-hom-cospan s t (map-equiv e))

  equiv-equiv-cospan :
    equiv-cospan → cospanning-type-cospan s ≃ cospanning-type-cospan t
  equiv-equiv-cospan = pr1

  map-equiv-cospan :
    equiv-cospan → cospanning-type-cospan s → cospanning-type-cospan t
  map-equiv-cospan e = map-equiv (equiv-equiv-cospan e)

  left-triangle-equiv-cospan :
    (e : equiv-cospan) → left-coherence-hom-cospan s t (map-equiv-cospan e)
  left-triangle-equiv-cospan e = pr1 (pr2 e)

  right-triangle-equiv-cospan :
    (e : equiv-cospan) → right-coherence-hom-cospan s t (map-equiv-cospan e)
  right-triangle-equiv-cospan e = pr2 (pr2 e)

  hom-equiv-cospan : equiv-cospan → hom-cospan s t
  pr1 (hom-equiv-cospan e) = map-equiv-cospan e
  pr1 (pr2 (hom-equiv-cospan e)) = left-triangle-equiv-cospan e
  pr2 (pr2 (hom-equiv-cospan e)) = right-triangle-equiv-cospan e

  is-equiv-equiv-cospan :
    (e : equiv-cospan) → is-equiv-hom-cospan s t (hom-equiv-cospan e)
  is-equiv-equiv-cospan e = is-equiv-map-equiv (equiv-equiv-cospan e)

  compute-equiv-cospan :
    Σ (hom-cospan s t) (is-equiv-hom-cospan s t) ≃ equiv-cospan
  compute-equiv-cospan = equiv-right-swap-Σ
```

### The identity equivalence of cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  id-equiv-cospan : (c : cospan l3 A B) → equiv-cospan c c
  pr1 (id-equiv-cospan c) = id-equiv
  pr1 (pr2 (id-equiv-cospan c)) = refl-htpy
  pr2 (pr2 (id-equiv-cospan c)) = refl-htpy
```

## Properties

### Characterizing equality of cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-eq-cospan : (c d : cospan l3 A B) → c ＝ d → equiv-cospan c d
  equiv-eq-cospan c .c refl = id-equiv-cospan c

  abstract
    is-torsorial-equiv-cospan :
      (c : cospan l3 A B) → is-torsorial (equiv-cospan {l1} {l2} {l3} {l3} c)
    is-torsorial-equiv-cospan c =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (pr1 c))
        ( cospanning-type-cospan c , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy' (left-map-cospan c))
          ( left-map-cospan c , refl-htpy)
          ( is-torsorial-htpy' (right-map-cospan c)))

  abstract
    is-equiv-equiv-eq-cospan :
      (c d : cospan l3 A B) → is-equiv (equiv-eq-cospan c d)
    is-equiv-equiv-eq-cospan c =
      fundamental-theorem-id (is-torsorial-equiv-cospan c) (equiv-eq-cospan c)

  extensionality-cospan :
    (c d : cospan l3 A B) → (c ＝ d) ≃ (equiv-cospan c d)
  pr1 (extensionality-cospan c d) = equiv-eq-cospan c d
  pr2 (extensionality-cospan c d) = is-equiv-equiv-eq-cospan c d

  eq-equiv-cospan : (c d : cospan l3 A B) → equiv-cospan c d → c ＝ d
  eq-equiv-cospan c d = map-inv-equiv (extensionality-cospan c d)
```
