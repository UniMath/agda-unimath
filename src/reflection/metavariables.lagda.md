# Metavariables

```agda
module reflection.metavariables where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.identity-types
open import foundation.universe-levels

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
  primMetaEquality : Metavariable-Agda → Metavariable-Agda → bool
  primMetaLess : Metavariable-Agda → Metavariable-Agda → bool
  primShowMeta : Metavariable-Agda → String
  primMetaToNat : Metavariable-Agda → ℕ
  primMetaToNatInjective : ∀ a b → primMetaToNat a ＝ primMetaToNat b → a ＝ b

data Blocker-Agda : UU lzero where
  blocker-any : list Blocker-Agda → Blocker-Agda
  blocker-all : list Blocker-Agda → Blocker-Agda
  blocker-metavariable : Metavariable-Agda → Blocker-Agda

{-# BUILTIN AGDABLOCKER Blocker-Agda #-}
{-# BUILTIN AGDABLOCKERANY blocker-any #-}
{-# BUILTIN AGDABLOCKERALL blocker-all #-}
{-# BUILTIN AGDABLOCKERMETA blocker-metavariable #-}
```
