# Arguments

```agda
module reflection.arguments where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import lists.lists
open import foundation-core.dependent-pair-types
open import foundation.cartesian-product-types
open import foundation.booleans
open import foundation.universe-levels
open import foundation.strings
open import foundation.characters
open import foundation.floats
open import foundation.machine-integers
open import foundation.unit-type
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-integers

open import reflection.names
open import reflection.metavariables
open import reflection.fixity
```

</details>

## Idea

-- TODO

## Definition

```agda
-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : UU lzero where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′  #-}

-- Arguments can be relevant or irrelevant.
data Relevance : UU lzero where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments also have a quantity.
data Quantity : UU lzero where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

data Modality : UU lzero where
  modality : (r : Relevance) (q : Quantity) → Modality

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

data ArgInfo : UU lzero where
  arg-info : (v : Visibility) (m : Modality) → ArgInfo

data Arg {l} (A : UU l) : UU l where
  arg : (i : ArgInfo) (x : A) → Arg A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}
```
