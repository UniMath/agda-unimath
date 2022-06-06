{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtruncationZ45Zlevels where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels

-- foundation.truncation-levels.truncation-level-ℕ
d_truncation'45'level'45'ℕ_4 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4
d_truncation'45'level'45'ℕ_4 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8
             (coe d_truncation'45'level'45'ℕ_4 (coe v1))
