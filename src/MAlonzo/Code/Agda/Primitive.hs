{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Agda.Primitive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Agda.Primitive.Level
type T_Level_14 = ()
d_Level_14
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Primitive.Level"
-- Agda.Primitive.lzero
d_lzero_16 = ()
-- Agda.Primitive.lsuc
d_lsuc_20 = (\ _ -> ())
-- Agda.Primitive._⊔_
d__'8852'__26 = (\ _ _ -> ())
