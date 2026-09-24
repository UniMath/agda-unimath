# The algebraic theory of left modules over commutative rings

```agda
module universal-algebra.algebraic-theory-of-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.equivalences
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings

open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-left-modules-rings
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The
{{#concept "algebraic theory of left modules over a commutative ring" Agda=algebraic-theory-left-module-Commutative-Ring}}
`R` is identical to the
[algebraic theory of left modules](universal-algebra.algebraic-theory-of-left-modules-rings.md)
over `R` as a [ring](ring-theory.rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  signature-left-module-Commutative-Ring : signature l
  signature-left-module-Commutative-Ring =
    signature-left-module-Ring (ring-Commutative-Ring R)

  algebraic-theory-left-module-Commutative-Ring :
    Algebraic-Theory l signature-left-module-Commutative-Ring
  algebraic-theory-left-module-Commutative-Ring =
    algebraic-theory-left-module-Ring (ring-Commutative-Ring R)

Algebra-Left-Module-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
Algebra-Left-Module-Commutative-Ring l2 R =
  Algebra-Left-Module-Ring l2 (ring-Commutative-Ring R)
```

## Properties

### Left modules from algebras in the theory of left modules over a commutative ring

```agda
left-module-Algebra-Left-Module-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) →
  Algebra-Left-Module-Commutative-Ring l2 R →
  left-module-Commutative-Ring l2 R
left-module-Algebra-Left-Module-Commutative-Ring R =
  left-module-Algebra-Left-Module-Ring (ring-Commutative-Ring R)
```

### Algebras in the theory of left modules from left modules over a commutative ring

```agda
algebra-left-module-left-module-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) →
  left-module-Commutative-Ring l2 R →
  Algebra-Left-Module-Commutative-Ring l2 R
algebra-left-module-left-module-Commutative-Ring R =
  algebra-left-module-left-module-Ring (ring-Commutative-Ring R)
```

### The type of left modules over a commutative ring is equivalent to the type of algebras in the theory of left modules

```agda
equiv-left-module-Algebra-Left-Module-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) →
  left-module-Commutative-Ring l2 R ≃ Algebra-Left-Module-Commutative-Ring l2 R
equiv-left-module-Algebra-Left-Module-Commutative-Ring R =
  equiv-left-module-Algebra-Left-Module-Ring (ring-Commutative-Ring R)
```

### Linear maps between left modules are equivalent to homomorphisms of algebras

```agda
hom-Algebra-Left-Module-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) →
  Algebra-Left-Module-Commutative-Ring l2 R →
  Algebra-Left-Module-Commutative-Ring l3 R →
  UU (l1 ⊔ l2 ⊔ l3)
hom-Algebra-Left-Module-Commutative-Ring R =
  hom-Algebra-Left-Module-Ring (ring-Commutative-Ring R)

linear-map-left-module-hom-Algebra-Left-Module-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (A : Algebra-Left-Module-Commutative-Ring l2 R)
  (B : Algebra-Left-Module-Commutative-Ring l3 R) →
  hom-Algebra-Left-Module-Commutative-Ring R A B →
  linear-map-left-module-Commutative-Ring
    ( R)
    ( left-module-Algebra-Left-Module-Commutative-Ring R A)
    ( left-module-Algebra-Left-Module-Commutative-Ring R B)
linear-map-left-module-hom-Algebra-Left-Module-Commutative-Ring R =
  linear-map-left-module-hom-Algebra-Left-Module-Ring (ring-Commutative-Ring R)

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  hom-algebra-left-module-linear-map-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R M N →
    hom-Algebra-Left-Module-Commutative-Ring
      ( R)
      ( algebra-left-module-left-module-Commutative-Ring R M)
      ( algebra-left-module-left-module-Commutative-Ring R N)
  hom-algebra-left-module-linear-map-left-module-Commutative-Ring =
    hom-algebra-left-module-linear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( N)

  equiv-linear-map-hom-algebra-Left-Module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R M N ≃
    hom-Algebra-Left-Module-Commutative-Ring
      ( R)
      ( algebra-left-module-left-module-Commutative-Ring R M)
      ( algebra-left-module-left-module-Commutative-Ring R N)
  equiv-linear-map-hom-algebra-Left-Module-Commutative-Ring =
    equiv-linear-map-hom-algebra-Left-Module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( N)
```
