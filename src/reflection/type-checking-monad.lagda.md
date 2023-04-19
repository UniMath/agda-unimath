# The type checking monad

```agda
module reflection.type-checking-monad where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.characters
open import foundation.floats
open import foundation.identity-types
open import foundation.machine-integers
open import foundation.propositional-truncations
open import foundation.strings
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.dependent-pair-types

open import group-theory.precategory-of-groups

open import lists.lists

open import reflection.abstractions
open import reflection.arguments
open import reflection.definitions
open import reflection.fixity
open import reflection.literals
open import reflection.metavariables
open import reflection.names
open import reflection.terms

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

-- TODO

## Definition

## The TC monad

To drive meta computations, we have the TC monad, reflecting Agda's `TCM` monad.

```agda
data ErrorPart : UU lzero where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  pattErr : Pattern → ErrorPart
  nameErr : Name → ErrorPart

postulate
  TC               : ∀ {a} → UU a → UU a
  returnTC         : ∀ {a} {A : UU a} → A → TC A
  bindTC           : ∀ {a b} {A : UU a} {B : UU b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC unit
  typeError        : ∀ {a} {A : UU a} → list ErrorPart → TC A
  inferType        : Term → TC Term
  checkType        : Term → Term → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : UU a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : UU a} → A → TC Term
  unquoteTC        : ∀ {a} {A : UU a} → Term → TC A
  quoteωTC         : ∀ {A : UUω} → A → TC Term
  getContext       : TC Telescope
  extendContext    : ∀ {a} {A : UU a} → String → Arg Term → TC A → TC A
  inContext        : ∀ {a} {A : UU a} → Telescope → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → Term → TC unit
  declarePostulate : Arg Name → Term → TC unit
  defineFun        : Name → list Clause → TC unit
  getType          : Name → TC Term
  getDefinition    : Name → TC Definition
  blockOnMeta      : ∀ {a} {A : UU a} → Meta → TC A
  commitTC         : TC unit
  isMacro          : Name → TC bool

  formatErrorParts : list ErrorPart → TC String

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → ℕ → list ErrorPart → TC unit

  -- If 'true', makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : UU a} → bool → TC A → TC A
  askNormalisation  : TC bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : UU a} → bool → TC A → TC A
  askReconstructed  : TC bool

  -- Whether implicit arguments at the end should be turned into metavariables
  withExpandLast : ∀ {a} {A : UU a} → bool → TC A → TC A
  askExpandLast  : TC bool

  -- White/blacklist specific definitions for reduction while executing the TC computation
  -- 'true' for whitelist, 'false' for blacklist
  withReduceDefs : ∀ {a} {A : UU a} → (Σ bool λ _ → list Name) → TC A → TC A
  askReduceDefs  : TC (Σ bool λ _ → list Name)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : UU a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : UU a} → TC (Σ A λ _ → bool) → TC A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
  getInstances : Meta → TC (list Term)

  declareData      : Name → ℕ → Term → TC unit
  defineData       : Name → list (Σ Name (λ _ → Term)) → TC unit
```

<details>
<summary>And now we bind the whole shebang above to the
`BUILTIN`{.agda}s that Agda knows about.
</summary>

```agda
{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

{-# BUILTIN AGDATCM                           TC                         #-}
{-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
{-# BUILTIN AGDATCMBIND                       bindTC                     #-}
{-# BUILTIN AGDATCMUNIFY                      unify                      #-}
{-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
{-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
{-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
{-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
{-# BUILTIN AGDATCMBLOCKONMETA                blockOnMeta                #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS           formatErrorParts           #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED          withReconstructed          #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST             withExpandLast             #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS             withReduceDefs             #-}
{-# BUILTIN AGDATCMASKNORMALISATION           askNormalisation           #-}
{-# BUILTIN AGDATCMASKRECONSTRUCTED           askReconstructed           #-}
{-# BUILTIN AGDATCMASKEXPANDLAST              askExpandLast              #-}
{-# BUILTIN AGDATCMASKREDUCEDEFS              askReduceDefs              #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
{-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}
{-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
{-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}
```
