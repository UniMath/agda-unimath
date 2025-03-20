# Metavariables

```agda
module reflection.metavariables where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.universe-levels

open import foundation-core.identity-types

open import lists.lists

open import primitives.strings
```

</details>

## Idea

The `Metavariable-Agda` type represents metavariables in Agda.

## Definition

```agda
postulate
  Metavariable-Agda : UU lzero

{-# BUILTIN AGDAMETA Metavariable-Agda #-}

primitive
  primMetaEquality :
    Metavariable-Agda → Metavariable-Agda → bool
  primMetaLess :
    Metavariable-Agda → Metavariable-Agda → bool
  primShowMeta :
    Metavariable-Agda → String
  primMetaToNat :
    Metavariable-Agda → ℕ
  primMetaToNatInjective :
    (a b : Metavariable-Agda) → primMetaToNat a ＝ primMetaToNat b → a ＝ b

data Blocker-Agda : UU lzero where
  any-Blocker-Agda : list Blocker-Agda → Blocker-Agda
  all-Blocker-Agda : list Blocker-Agda → Blocker-Agda
  metavariable-Blocker-Agda : Metavariable-Agda → Blocker-Agda

{-# BUILTIN AGDABLOCKER Blocker-Agda #-}
{-# BUILTIN AGDABLOCKERANY any-Blocker-Agda #-}
{-# BUILTIN AGDABLOCKERALL all-Blocker-Agda #-}
{-# BUILTIN AGDABLOCKERMETA metavariable-Blocker-Agda #-}
```
