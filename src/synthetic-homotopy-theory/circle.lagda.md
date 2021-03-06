---
title: The circle
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.circle where

open import foundation.0-connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

## Postulates

```agda
postulate ๐ยน : UU lzero

postulate base-๐ยน : ๐ยน

postulate loop-๐ยน : Id base-๐ยน base-๐ยน

free-loop-๐ยน : free-loop ๐ยน
pr1 free-loop-๐ยน = base-๐ยน
pr2 free-loop-๐ยน = loop-๐ยน

๐ยน-Pointed-Type : Pointed-Type lzero
pr1 ๐ยน-Pointed-Type = ๐ยน
pr2 ๐ยน-Pointed-Type = base-๐ยน

postulate ind-๐ยน : {l : Level} โ induction-principle-circle l free-loop-๐ยน
```

## Properties

### The dependent universal property of the circle

```agda
dependent-universal-property-๐ยน :
  {l : Level} โ dependent-universal-property-circle l free-loop-๐ยน
dependent-universal-property-๐ยน =
  dependent-universal-property-induction-principle-circle free-loop-๐ยน ind-๐ยน

uniqueness-dependent-universal-property-๐ยน :
  {l : Level} {P : ๐ยน โ UU l} (k : free-dependent-loop free-loop-๐ยน P) โ
  is-contr
    ( ฮฃ ( (x : ๐ยน) โ P x)
        ( ฮป h โ
          Eq-free-dependent-loop free-loop-๐ยน P
            ( ev-free-loop-ฮ? free-loop-๐ยน P h) k))
uniqueness-dependent-universal-property-๐ยน {l} {P} =
  uniqueness-dependent-universal-property-circle
    free-loop-๐ยน
    dependent-universal-property-๐ยน

module _
  {l : Level} (P : ๐ยน โ UU l) (p0 : P base-๐ยน) (ฮฑ : Id (tr P loop-๐ยน p0) p0)
  where

  ฮ?-๐ยน : UU l
  ฮ?-๐ยน =
    ฮฃ ( (x : ๐ยน) โ P x)
      ( ฮป h โ
        Eq-free-dependent-loop free-loop-๐ยน P
          ( ev-free-loop-ฮ? free-loop-๐ยน P h) (pair p0 ฮฑ))

  apply-dependent-universal-property-๐ยน : ฮ?-๐ยน
  apply-dependent-universal-property-๐ยน =
    center (uniqueness-dependent-universal-property-๐ยน (pair p0 ฮฑ))
  
  function-apply-dependent-universal-property-๐ยน : (x : ๐ยน) โ P x
  function-apply-dependent-universal-property-๐ยน =
    pr1 apply-dependent-universal-property-๐ยน

  base-dependent-universal-property-๐ยน :
    Id (function-apply-dependent-universal-property-๐ยน base-๐ยน) p0
  base-dependent-universal-property-๐ยน =
    pr1 (pr2 apply-dependent-universal-property-๐ยน)

  loop-dependent-universal-property-๐ยน :
    Id ( apd function-apply-dependent-universal-property-๐ยน loop-๐ยน โ
         base-dependent-universal-property-๐ยน)
       ( ap (tr P loop-๐ยน) base-dependent-universal-property-๐ยน โ ฮฑ)
  loop-dependent-universal-property-๐ยน =
    pr2 (pr2 apply-dependent-universal-property-๐ยน)
```

### The universal property of the circle

```agda
universal-property-๐ยน :
  {l : Level} โ universal-property-circle l free-loop-๐ยน
universal-property-๐ยน =
  universal-property-dependent-universal-property-circle
    free-loop-๐ยน
    dependent-universal-property-๐ยน

uniqueness-universal-property-๐ยน :
  {l : Level} {X : UU l} (ฮฑ : free-loop X) โ
  is-contr
    ( ฮฃ ( ๐ยน โ X)
        ( ฮป h โ Eq-free-loop (ev-free-loop free-loop-๐ยน X h) ฮฑ))
uniqueness-universal-property-๐ยน {l} {X} =
  uniqueness-universal-property-circle free-loop-๐ยน universal-property-๐ยน X

module _
  {l : Level} {X : UU l} (x : X) (ฮฑ : Id x x)
  where

  Map-๐ยน : UU l
  Map-๐ยน =
    ฮฃ ( ๐ยน โ X)
      ( ฮป h โ Eq-free-loop (ev-free-loop free-loop-๐ยน X h) (pair x ฮฑ))

  apply-universal-property-๐ยน : Map-๐ยน
  apply-universal-property-๐ยน =
    center (uniqueness-universal-property-๐ยน (pair x ฮฑ))
      
  map-apply-universal-property-๐ยน : ๐ยน โ X
  map-apply-universal-property-๐ยน =
    pr1 apply-universal-property-๐ยน

  base-universal-property-๐ยน :
    Id (map-apply-universal-property-๐ยน base-๐ยน) x
  base-universal-property-๐ยน =
    pr1 (pr2 apply-universal-property-๐ยน)

  loop-universal-property-๐ยน :
    Id ( ap map-apply-universal-property-๐ยน loop-๐ยน โ
         base-universal-property-๐ยน)
       ( base-universal-property-๐ยน โ ฮฑ)
  loop-universal-property-๐ยน =
    pr2 (pr2 apply-universal-property-๐ยน)
```

### The circle is 0-connected

```agda
mere-eq-๐ยน : (x y : ๐ยน) โ mere-eq x y
mere-eq-๐ยน =
  function-apply-dependent-universal-property-๐ยน
    ( ฮป x โ (y : ๐ยน) โ mere-eq x y)
    ( function-apply-dependent-universal-property-๐ยน
      ( mere-eq base-๐ยน)
      ( refl-mere-eq)
      ( eq-is-prop is-prop-type-trunc-Prop))
    ( eq-is-prop (is-prop-ฮ? (ฮป y โ is-prop-type-trunc-Prop)))

is-0-connected-๐ยน : is-0-connected ๐ยน
is-0-connected-๐ยน = is-0-connected-mere-eq base-๐ยน (mere-eq-๐ยน base-๐ยน)
```
