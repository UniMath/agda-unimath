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

The `Meta` type represents metavariables in Agda.

## Definition

```agda
postulate
  Meta : UU lzero

{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → bool
  primMetaLess : Meta → Meta → bool
  primShowMeta : Meta → String
  primMetaToNat : Meta → ℕ
  primMetaToNatInjective :
    (a b : Meta) → primMetaToNat a ＝ primMetaToNat b → a ＝ b

data Blocker : UU lzero where
  blocker-any : list Blocker → Blocker
  blocker-all : list Blocker → Blocker
  blocker-meta : Meta → Blocker

{-# BUILTIN AGDABLOCKER Blocker #-}
{-# BUILTIN AGDABLOCKERANY blocker-any #-}
{-# BUILTIN AGDABLOCKERALL blocker-all #-}
{-# BUILTIN AGDABLOCKERMETA blocker-meta #-}
```
